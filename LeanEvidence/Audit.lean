module

public meta import LeanEvidence.Commands

public section
meta section

open Lean

namespace LeanEvidence.Audit

private def terminates (env : Environment) (name : Name) : Bool :=
  (Elab.Structural.eqnInfoExt.find? env name).isSome || (Elab.WF.eqnInfoExt.find? env name).isSome

private def computational (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do return false
  if ← Meta.isProp info.type then return false
  Meta.forallTelescopeReducing info.type fun _ result => return !(← Meta.whnf result).isSort

/-- The constants from which `IO.RealWorld` is reachable through constructors and definition
bodies, starting from the types of `infos`: a walk forward records the users of each constant,
then a walk back from `IO.RealWorld` collects every user. -/
private def effectful (env : Environment) (infos : Array ConstantInfo) : NameSet := Id.run do
  let mut pending := infos.flatMap (·.type.getUsedConstants)
  let mut seen : NameSet := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let uses := match env.find? name with
      | some (.inductInfo ind) => ind.ctors.toArray
      | some (.ctorInfo constructor) => constructor.type.getUsedConstants
      | some info => ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      | none => #[]
    for used in uses do users := users.insert used ((users.getD used #[]).push name)
    pending := pending ++ uses
  let mut reached : NameSet := {}
  pending := #[``IO.RealWorld]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if reached.contains name then continue
    reached := reached.insert name
    pending := pending ++ users.getD name #[]
  return reached

/-- The nonstandard axioms `name` depends on. An olean records the axioms of each declaration it
exports, so only private declarations are walked, each once; a cycle back to `name` contributes
nothing. -/
private partial def axiomsOf (name : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some found := (← get)[name]? then return found
  modify (·.insert name #[])
  let found ← if !isPrivateName name then nonstandardAxioms name else
    match (← getEnv).find? name with
    | none => pure #[]
    | some info => do
      let mut found := if info.isAxiom && !standardAxioms.contains name then #[name] else #[]
      let uses := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
        match info with | .inductInfo ind => ind.ctors.toArray | _ => #[]
      for used in uses do
        found := found ++ (← axiomsOf used).filter (!found.contains ·)
      pure found
  modify (·.insert name found)
  return found

private def declaration (reachesIO : NameSet) (info : ConstantInfo) (moduleName : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM DeclarationFact := do
  let env ← getEnv
  let generated := (← findDeclarationRangesCore? info.name).isNone
  let isComputational ← Meta.MetaM.run' <| computational info
  return {
    name := info.name
    moduleName
    computational := isComputational
    isUnsafe := info.isUnsafe
    isPartial := info.isPartial &&
      !(generated && (Compiler.isUnsafeRecName? info.name).any (terminates env))
    external := isExtern env info.name
    replaced := (Compiler.getImplementedBy? env info.name).isSome
    initializes := (getInitFnNameFor? env info.name).isSome
    effects := isComputational && info.type.getUsedConstants.any reachesIO.contains
    debug := info.getUsedConstantsAsSet.any fun n => n.isAtomic && "dbg".isPrefixOf n.toString
    axioms := ← axiomsOf info.name
  }

/-- Facts about each module of `catalog` and every declaration it compiles. -/
def collect (catalog : Array Name) : CoreM Inventory := do
  modifyEnv (·.setExporting false)
  let env ← getEnv
  let modules ← catalog.mapM fun name => do
    let some idx := env.getModuleIdx? name | throwError "Compiled module {name} is unavailable"
    return (name, env.header.moduleData[idx.toNat]!)
  let reachesIO := effectful env (modules.flatMap (·.2.constants))
  let declarations ← StateRefT'.run' (s := {}) <| modules.flatMapM fun (name, data) =>
    data.constants.mapM fun info => declaration reachesIO info name
  return {
    modules := modules.map fun (name, data) =>
      { name, usesModuleSystem := data.isModule,
        imports := data.imports.map fun i => { name := i.module, comptime := i.isMeta } }
    declarations }

def withEnvironment {α : Type} (modules : Array Name) (action : CoreM α) : IO α := do
  unsafe enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let (result, _) ← action.toIO { fileName := "<lean-evidence>", fileMap := default, maxHeartbeats := 0 } { env }
  return result

def violations (project : Project) (inventory : Inventory) : Array String := Id.run do
  let mut errors := #[]
  for fact in inventory.modules do
    let some role := project.role? fact.name
      | errors := errors.push s!"Unclassified module {fact.name}"
    unless fact.usesModuleSystem do errors := errors.push s!"{fact.name}: start the file with `module`"
    for dependency in fact.imports do
      unless project.admits role dependency do
        errors := errors.push s!"{fact.name} ({repr role}) may not import {dependency.name}"
  for fact in inventory.declarations do
    if let some role := project.role? fact.moduleName then
      let reasons := fact.reasons role
      unless reasons.isEmpty do
        errors := errors.push s!"{fact.name} ({repr role}): {", ".intercalate reasons}"
  return errors

structure Config where
  challenge_module : Name
  solution_module : Name
  theorem_names : Array Name
  definition_names : Option (Array Name)
  deriving FromJson

structure Headline where
  name : Name
  premises : Array Premise
  unnamed : Array String

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
    let mut unnamed := #[]
    for binder in binders do
      let statement ← Meta.inferType binder
      let claim := statement.getAppFn.constName
      if let some kind := claimKind? (← getEnv) claim then
        premises := premises.push { claim, kind, discharged := ← discharged statement }
      else if !statement.hasFVar && (← Meta.isProp statement) then
        unnamed := unnamed.push (toString (← Meta.ppExpr statement))
    return { name, premises, unnamed }

def headlineViolations (project : Project) (holes : Array Name) (headlines : Array Headline)
    (evidence : Array Evidence) : MetaM (Array String) := do
  let mut errors := #[]
  for (claim, _) in registeredClaims (← getEnv) do
    if let some role := (← findModuleOf? claim).bind project.role? then
      unless role == .spec do errors := errors.push s!"{claim}: declare claims in a spec module"
  for hole in holes do
    unless (← findModuleOf? hole).bind project.role? matches some .core | some .shell do
      errors := errors.push s!"{hole}: a definition hole must be a core or shell definition"
  for line in headlines do
    for hypothesis in line.unnamed do
      errors := errors.push s!"{line.name}: hypothesis {hypothesis} is not a WorldClaim or Conjecture"
    for premise in line.premises do
      if premise.kind == .world && !evidence.any (·.claim == premise.claim) then
        errors := errors.push
          s!"{line.name}: world assumption {premise.claim} has no Test, Check, or live suite"
  return errors

def challengeImports (project : Project) (root : Name) : IO (Array String) := do
  let path := (← (← getSrcSearchPath).findWithExt "lean" root).getD (modToFilePath "." root "lean")
  let header ← parseImports' (← IO.FS.readFile path) path.toString
  return header.imports.filterMap fun dependency =>
    if project.admits .spec { name := dependency.module, comptime := false } then none
    else some s!"{root} imports {dependency.module}; \
      a challenge may import only spec and boundary modules and trusted roots"

private def describe (evidence : Array Evidence) (premise : Premise) : String :=
  let count := fun kind => (evidence.filter fun e => e.claim == premise.claim && e.kind == kind).size
  let kind := if premise.kind == .world then "world" else if premise.discharged then "proved" else "open"
  s!"{kind} {premise.claim} [{count .test} tests, {count .check} checks, {count .suite} suites]"

def run (project : Project) (args : List String) : IO Unit := do
  let config : Config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json") >>= fromJson?
  let catalog := args.toArray.map String.toName
  unless catalog.contains config.solution_module do
    throw <| .userError s!"solution_module {config.solution_module} is not built by a default target"
  let (inventory, evidence, headlines, headlineErrors) ← withEnvironment catalog <| Meta.MetaM.run' do
    let inventory ← collect catalog
    let evidence := allEvidence (← getEnv)
    let headlines ← config.theorem_names.mapM headline
    let holes := config.definition_names.getD #[]
    return (inventory, evidence, headlines, ← headlineViolations project holes headlines evidence)
  let errors := violations project inventory ++ headlineErrors ++
    (← challengeImports project config.challenge_module)
  unless project.check inventory && errors.isEmpty do
    throw <| IO.userError ("LeanEvidence audit failed:\n" ++ "\n".intercalate errors.toList)
  IO.println s!"Checked {inventory.modules.size} modules and {inventory.declarations.size} declarations"
  for line in headlines do
    let premises := "; ".intercalate (line.premises.map (describe evidence)).toList
    IO.println (s!"{if proved line.premises then "●" else "◕"} {line.name}" ++
      if premises.isEmpty then "" else s!"  ({premises})")

end LeanEvidence.Audit
