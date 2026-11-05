module

public meta import LeanEvidence.Policy
public meta import LeanEvidence.Commands
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns

public section
meta section

open Lean

namespace LeanEvidence.Audit

private def owner? (env : Environment) (name : Name) : Option Name :=
  env.getModuleIdxFor? name |>.bind fun idx => env.allImportedModuleNames[idx.toNat]?

private def terminates (env : Environment) (name : Name) : Bool :=
  (Elab.Structural.eqnInfoExt.find? env name).isSome || (Elab.WF.eqnInfoExt.find? env name).isSome

private def recursionParent? (env : Environment) (info : ConstantInfo) : CoreM (Option Name) := do
  let some parent := Compiler.isUnsafeRecName? info.name | return none
  let some parentInfo := env.find? parent | return none
  unless !parentInfo.isUnsafe && owner? env parent == owner? env info.name &&
      (← findDeclarationRangesCore? info.name).isNone do return none
  return some parent

private def computational (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do return false
  if ← Meta.isProp info.type then return false
  Meta.forallTelescopeReducing info.type fun _ result => return !(← Meta.whnf result).isSort

private def effects (env : Environment) (type : Expr) : Bool := Id.run do
  let mut pending := type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == ``IO.RealWorld then return true
    if let some info := env.find? name then
      if let .inductInfo ind := info then pending := pending ++ ind.ctors.toArray
      if let .ctorInfo constructor := info then pending := pending ++ constructor.type.getUsedConstants
      if let some body := info.value? (allowOpaque := true) then pending := pending ++ body.getUsedConstants
  return false

private def declaration (project : Project) (info : ConstantInfo) (moduleName : Name) :
    CoreM DeclarationFact := do
  let env ← getEnv
  let isComputational ← Meta.MetaM.run' <| computational info
  let parent ← recursionParent? env info
  let ownRecursion := (Compiler.getImplementedBy? env info.name).any fun impl =>
    Compiler.isUnsafeRecName? impl == some info.name
  let replacement := (Compiler.getImplementedBy? env info.name).filter fun _ => !ownRecursion
  return {
    name := info.name
    moduleName
    computational := isComputational
    isUnsafe := parent.isNone && info.isUnsafe
    isPartial := match parent with
      | some name => !terminates env name
      | none => info.isPartial || (ownRecursion && !terminates env info.name)
    external := isExtern env info.name
    replaced := replacement.isSome
    initializes := (getInitFnNameFor? env info.name).isSome ||
      (getBuiltinInitFnNameFor? env info.name).isSome
    effects := isComputational && effects env info.type
    forbidden := info.getUsedConstantsAsSet.toArray.filter project.forbidden.contains
    axioms := ← collectAxioms info.name
  }

def collect (project : Project) (catalog : Array Name) : CoreM Inventory := do
  modifyEnv (·.setExporting false)
  let env ← getEnv
  let modules ← catalog.mapM fun name => do
    let some idx := env.getModuleIdx? name | throwError "Compiled module {name} is unavailable"
    let data := env.header.moduleData[idx.toNat]!
    return {
      name
      usesModuleSystem := data.isModule
      imports := data.imports.map fun dependency =>
        { name := dependency.module, comptime := dependency.isMeta }
    }
  let mut declarations := #[]
  for (name, info) in env.constants.toList do
    if let some moduleName := owner? env name then
      if catalog.contains moduleName then
        declarations := declarations.push
          (← withCurrHeartbeats <| declaration project info moduleName)
  return { modules, declarations }

def withEnvironment {α : Type} (imports : Array Import) (action : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let imports := imports.map ({ · with importAll := true })
  let env ← withImporting do
    let (_, state) ← (importModulesCore imports).run
    finalizeImport state imports {} (leakEnv := false) (loadExts := true) (isModule := true)
  let (result, _) ← action.toIO { fileName := "<lean-evidence>", fileMap := default } { env }
  return result

private def merge (left right : DeclarationFact) : DeclarationFact := {
  left with
  computational := left.computational || right.computational
  isUnsafe := left.isUnsafe || right.isUnsafe
  isPartial := left.isPartial || right.isPartial
  external := left.external || right.external
  replaced := left.replaced || right.replaced
  initializes := left.initializes || right.initializes
  effects := left.effects || right.effects
  forbidden := right.forbidden.foldl (fun names n => if names.contains n then names else names.push n)
    left.forbidden
  axioms := right.axioms.foldl (fun names n => if names.contains n then names else names.push n)
    left.axioms
}

structure Inspection where
  inventory : Inventory
  evidence : Array Evidence
  deriving Inhabited

def inspect (project : Project) (catalog : Array Name) : IO Inspection := do
  let mut imported : NameSet := {}
  for root in catalog do
    let reached ← withEnvironment #[{ module := root }] do
      let env ← getEnv
      return catalog.filter fun name => name != root && (env.getModuleIdx? name).isSome
    for name in reached do imported := imported.insert name
  let mut modules : Std.HashMap Name ModuleFact := {}
  let mut declarations : Std.HashMap (Name × Name) DeclarationFact := {}
  let mut evidence : Array Evidence := #[]
  for root in catalog.filter (!imported.contains ·) do
    let (inventory, found) ← withEnvironment #[{ module := root }] do
      let env ← getEnv
      return (← collect project (catalog.filter fun name => (env.getModuleIdx? name).isSome),
        allEvidence env)
    for entry in found do
      unless evidence.any (fun e => e.claim == entry.claim && e.statement == entry.statement &&
          e.kind == entry.kind) do
        evidence := evidence.push entry
    for fact in inventory.modules do modules := modules.insert fact.name fact
    for fact in inventory.declarations do
      let key := (fact.moduleName, fact.name)
      declarations := declarations.insert key ((declarations[key]?).map (merge · fact) |>.getD fact)
  return {
    inventory := {
      modules := modules.toArray.map (·.2) |>.qsort (·.name.toString < ·.name.toString)
      declarations := declarations.toArray.map (·.2) |>.qsort (·.name.toString < ·.name.toString)
    }
    evidence
  }

def violations (project : Project) (catalog : Array Name) (inventory : Inventory) :
    Array String := Id.run do
  let mut errors := #[]
  let layers := project.layers.map (·.1)
  for layer in layers do
    if (layers.filter (· == layer)).size > 1 then errors := errors.push s!"Duplicate layer {layer}"
  for name in catalog do
    if (project.role? name).isNone then errors := errors.push s!"Unclassified module {name}"
    unless inventory.modules.any (·.name == name) do errors := errors.push s!"Missing module {name}"
  for fact in inventory.modules do
    let some role := project.role? fact.name | continue
    unless fact.usesModuleSystem do errors := errors.push s!"{fact.name}: start the file with `module`"
    for dependency in fact.imports do
      unless project.admits role dependency do
        errors := errors.push s!"{fact.name} ({repr role}) may not import {dependency.name}"
  for fact in inventory.declarations do
    let some role := project.role? fact.moduleName
      | errors := errors.push s!"{fact.name}: unclassified module {fact.moduleName}"
    if fact.admitted role then continue
    let mut reasons := #[]
    unless fact.standard do
      reasons := reasons.push s!"axioms {fact.axioms.filter (!standardAxioms.contains ·)}"
    if fact.computational then
      if fact.isUnsafe then reasons := reasons.push "unsafe"
      if fact.isPartial then reasons := reasons.push "partial"
      if fact.external then reasons := reasons.push "@[extern]"
      if fact.replaced then reasons := reasons.push "@[implemented_by]"
      if fact.initializes then reasons := reasons.push "initializer"
      if fact.effects then reasons := reasons.push "IO"
      unless fact.forbidden.isEmpty do reasons := reasons.push s!"uses {fact.forbidden}"
      if role == .boundary && !fact.external then reasons := reasons.push "not an @[extern] binding"
    errors := errors.push s!"{fact.name} ({repr role}): {String.intercalate ", " reasons.toList}"
  return errors

structure Config where
  challenge : Name
  solution : Name
  theorems : Array Name
  holes : Array Name
  deriving Inhabited, Repr

def readConfig (path : System.FilePath) : IO Config := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let names (field : String) : IO (Array Name) := do
    let values ← IO.ofExcept <| json.getObjValAs? (Array String) field
    return values.map String.toName
  return {
    challenge := (← IO.ofExcept <| json.getObjValAs? String "challenge_module").toName
    solution := (← IO.ofExcept <| json.getObjValAs? String "solution_module").toName
    theorems := ← names "theorem_names"
    holes := ((json.getObjValAs? (Array String) "definition_names").toOption.getD #[]).map
      String.toName
  }

structure Headline where
  name : Name
  premises : Array Premise
  deriving Inhabited, Repr

private def discharged (statement : Expr) : CoreM Bool := do
  if statement.hasFVar || statement.hasMVar then return false
  for (_, info) in (← getEnv).constants.toList do
    if info.isTheorem && info.type == statement then
      if (← nonstandardAxioms info.name).isEmpty then return true
  return false

def headline (name : Name) : MetaM Headline := do
  let some info := (← getEnv).find? name | throwError "Headline {name} is not compiled"
  Meta.forallTelescope info.type fun binders _ => do
    let mut premises := #[]
    for binder in binders do
      let statement ← instantiateMVars (← Meta.inferType binder)
      let some claim := statement.getAppFn.constName? | continue
      let some kind := claimKind? (← getEnv) claim | continue
      premises := premises.push { claim, kind, discharged := ← discharged statement }
    return { name, premises }

private partial def challengeImports (project : Project) (root : Name) (pending : List Name)
    (seen : NameSet) (errors : Array String) : IO (Array String) := do
  match pending with
  | [] => return errors
  | name :: rest =>
    if seen.contains name then return ← challengeImports project root rest seen errors
    let path : System.FilePath := (name.toString.replace "." "/") ++ ".lean"
    let header ← parseImports' (← IO.FS.readFile path) path.toString
    let mut errors := errors
    let mut next := rest
    for dependency in header.imports do
      let target := dependency.module
      if root.isPrefixOf target then
        next := target :: next
      else
        match project.role? target with
        | some .spec | some .boundary => pure ()
        | some role =>
          errors := errors.push s!"{name} imports {target} ({repr role}); \
            a challenge may import only spec and boundary modules"
        | none =>
          unless project.trusts target do
            errors := errors.push s!"{name} imports untrusted {target}"
    challengeImports project root next (seen.insert name) errors

def headlineViolations (project : Project) (config : Config) (headlines : Array Headline)
    (evidence : Array Evidence) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  for (claim, _) in registeredClaims env do
    if let some moduleName := owner? env claim then
      if let some role := project.role? moduleName then
        unless role == .spec do
          errors := errors.push s!"{claim}: declare claims in a spec module, not {moduleName}"
  for hole in config.holes do
    match (owner? env hole).bind project.role? with
    | some .core | some .shell => pure ()
    | _ => errors := errors.push s!"{hole}: a definition hole must be a core or shell definition"
  for line in headlines do
    for premise in line.premises do
      if premise.kind == .world && !evidence.any (·.claim == premise.claim) then
        errors := errors.push
          s!"{line.name}: world assumption {premise.claim} has no Test, Check, or live suite"
  return errors

private def describe (evidence : Array Evidence) (premise : Premise) : String :=
  let count := fun kind => (evidence.filter fun e => e.claim == premise.claim && e.kind == kind).size
  let kind := if premise.kind == .world then "world" else if premise.discharged then "proved" else "open"
  s!"{kind} {premise.claim} [{count .test} tests, {count .check} checks, {count .suite} suites]"

def run (project : Project) (catalog : Array Name) (configPath : System.FilePath := "comparator.json") :
    IO Unit := do
  let config ← readConfig configPath
  let { inventory, evidence } ← inspect project catalog
  let (lines, headlineErrors, report) ← withEnvironment #[{ module := config.solution }] do
    let lines ← Meta.MetaM.run' <| config.theorems.mapM headline
    let errors ← Meta.MetaM.run' <| headlineViolations project config lines evidence
    let report := lines.map fun line =>
      let mark := if level line.premises == .proved then "●" else "◕"
      let premises := line.premises.map (describe evidence)
      s!"{mark} {line.name}" ++
        (if premises.isEmpty then "" else s!"  ({String.intercalate "; " premises.toList})")
    return (lines, errors, report)
  let challengeErrors ← challengeImports project config.challenge [config.challenge] {} #[]
  let errors := (if project.check catalog inventory then #[] else
    let found := violations project catalog inventory
    if found.isEmpty then #["Project check failed"] else found) ++ headlineErrors ++ challengeErrors
  unless errors.isEmpty do
    throw <| IO.userError ("LeanEvidence audit failed:\n" ++ String.intercalate "\n" errors.toList)
  IO.println s!"Checked {inventory.modules.size} modules and {inventory.declarations.size} declarations"
  for line in report do IO.println line
  let proved := (lines.filter (level ·.premises == .proved)).size
  IO.println s!"{proved}/{lines.size} headline claims proved; the others depend on open conjectures"

end LeanEvidence.Audit
