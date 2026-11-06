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

private def meaningDependencies (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.inductInfo ind) => ind.ctors.toArray
  | some (.ctorInfo constructor) => constructor.type.getUsedConstants
  | some info => ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  | none => #[]

private def dependentsFrom (env : Environment) (roots : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut dependents : Std.HashMap Name (Array Name) := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let dependencies := meaningDependencies env name
    for dependency in dependencies do
      dependents := dependents.insert dependency ((dependents.getD dependency #[]).push name)
    pending := pending ++ dependencies
  return dependents

private def transitiveDependents (dependents : Std.HashMap Name (Array Name)) (target : Name) :
    NameSet := Id.run do
  let mut pending := #[target]
  let mut reached : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if reached.contains name then continue
    reached := reached.insert name
    pending := pending ++ dependents.getD name #[]
  return reached

private def recordedInOlean (name : Name) : Bool := !isPrivateName name

private partial def axiomsOf (name : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some known := (← get)[name]? then return known
  modify (·.insert name #[])
  let found ← if recordedInOlean name then nonstandardAxioms name else
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
    unfoldable := info matches .defnInfo _
    replaced := (Compiler.getImplementedBy? env info.name).isSome
    initializes := (getInitFnNameFor? env info.name).isSome
    effects := isComputational && info.type.getUsedConstants.any reachesIO.contains
    debug := info.getUsedConstantsAsSet.any fun n => n.isAtomic && "dbg".isPrefixOf n.toString
    axioms := ← axiomsOf info.name
  }

def collect (catalog : Array Name) : CoreM Inventory := do
  modifyEnv (·.setExporting false)
  let env ← getEnv
  let modules ← catalog.mapM fun name => do
    let some idx := env.getModuleIdx? name | throwError "Compiled module {name} is unavailable"
    return (name, env.header.moduleData[idx.toNat]!)
  let types := modules.flatMap fun (_, data) => data.constants.flatMap (·.type.getUsedConstants)
  let reachesIO := transitiveDependents (dependentsFrom env types) ``IO.RealWorld
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

private def runtimeCallees (env : Environment) (name : Name) : Array Name :=
  let body := ((env.find? name).bind (·.value? (allowOpaque := true))).map (·.getUsedConstants)
  body.getD #[] ++ (Compiler.getImplementedBy? env name).toArray

def reachedFrom (env : Environment) (catalog : Array Name) (root : Name) : NameSet := Id.run do
  let inCatalog := fun name =>
    (env.getModuleIdxFor? name).any fun idx => catalog.contains env.header.modules[idx.toNat]!.module
  let mut pending := #[root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name || !inCatalog name then continue
    seen := seen.insert name
    pending := pending ++ runtimeCallees env name
  return seen

def sound (project : Project) (inventory : Inventory) (holes : Array (Name × Option Role))
    (unreached : Array Name) (headlines : Array Headline) : Array String := Id.run do
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
  for (hole, role) in holes do
    unless role matches some .core | some .shell do
      errors := errors.push s!"{hole}: a definition hole must be a core or shell definition"
  for hole in unreached do
    errors := errors.push s!"{hole}: main never reaches this hole"
  for line in headlines do
    for hypothesis in line.unnamed do
      errors := errors.push s!"{line.name}: hypothesis {hypothesis} is not a WorldClaim or Conjecture"
  return errors

def owned (project : Project) (config : Config) (claims : Array (Name × Option Role))
    (challengeImports : Array Name) (declared : Array (Name × Bool)) : Array String := Id.run do
  let mut errors := #[]
  for (claim, role) in claims do
    if role.isSome && role != some .spec then
      errors := errors.push s!"{claim}: declare claims in a spec module"
  for dependency in challengeImports do
    unless project.admits .spec { name := dependency, comptime := false } do
      errors := errors.push s!"{config.challenge_module} imports {dependency}; \
        a challenge may import only spec and boundary modules and trusted roots"
  let holes := config.definition_names.getD #[]
  for (name, isTheorem) in declared do
    let (field, listed) := if isTheorem then ("theorem_names", config.theorem_names)
      else ("definition_names", holes)
    unless listed.contains name do
      errors := errors.push s!"{config.challenge_module} declares {name}, which comparator.json {field} omits"
  for name in config.theorem_names ++ holes do
    unless declared.any (·.1 == name) do
      errors := errors.push s!"comparator.json lists {name}, which {config.challenge_module} does not declare"
  return errors

def evidenced (headlines : Array Headline) (evidence : Array Evidence) : Array String :=
  headlines.flatMap fun line => line.premises.filterMap fun premise =>
    if premise.kind == .world && !evidence.any (·.claim == premise.claim) then
      some s!"{line.name}: world assumption {premise.claim} has no Test, Check, or live suite"
    else none

def challengeImports (challenge : Name) : IO (Array Name) := do
  let path := (← (← getSrcSearchPath).findWithExt "lean" challenge).getD
    (modToFilePath "." challenge "lean")
  return (← parseImports' (← IO.FS.readFile path) path.toString).imports.map (·.module)

def challengeDeclarations (challenge : Name) : IO (Array (Name × Bool)) := do
  let file ← findOLean challenge
  let parts ← readModuleDataParts #[file, file.addExtension "server", file.addExtension "private"]
  let some (data, _) := parts.back? | throw <| .userError s!"{challenge} is not compiled"
  return (data.constants.filter (!·.name.isInternal)).map fun info => (info.name, info.isTheorem)

private def sourceFile (module : Name) : String :=
  "/".intercalate (module.components.map toString) ++ ".lean"

def ownedFiles (project : Project) (inventory : Inventory) (challenge : Name) : IO (Array String) :=
  let claimModules := inventory.modules.filter (project.role? ·.name matches some .spec | some .boundary)
  (#["comparator.json", "Audit.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
    sourceFile challenge] ++ claimModules.map (sourceFile ·.name)).filterM (System.FilePath.pathExists ·)

private def describe (evidence : Array Evidence) (premise : Premise) : String :=
  let found := evidence.filter (·.claim == premise.claim)
  let count := fun kind => (found.filter (·.kind == kind)).size
  let suites := found.filterMap fun e => if e.kind == .suite then some (toString e.source) else none
  let kind := if premise.kind == .world then "world" else if premise.discharged then "proved" else "open"
  s!"{kind} {premise.claim} [{count .test} tests, {count .check} checks" ++
    (if suites.isEmpty then "]" else s!", suites {", ".intercalate suites.toList}]")

def run (project : Project) (args : List String) : IO Unit := do
  let config : Config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json") >>= fromJson?
  let catalog := args.toArray.map String.toName
  unless catalog.contains config.solution_module do
    throw <| .userError s!"solution_module {config.solution_module} is not built by a default target"
  let holes := config.definition_names.getD #[]
  let (inventory, evidence, headlines, holeRoles, claimRoles, unreached) ←
    withEnvironment catalog <| Meta.MetaM.run' do
      let env ← getEnv
      let roleOf (name : Name) : MetaM (Name × Option Role) := do
        return (name, (← findModuleOf? name).bind project.role?)
      let reached := reachedFrom env catalog `main
      return (← collect catalog, allEvidence env, ← config.theorem_names.mapM headline,
        ← holes.mapM roleOf, ← (registeredClaims env).mapM (roleOf ·.1),
        if env.contains `main then holes.filter (!reached.contains ·) else #[])
  let imports ← challengeImports config.challenge_module
  let failures :=
    (sound project inventory holeRoles unreached headlines).map ("sound: " ++ ·) ++
    (owned project config claimRoles imports (← challengeDeclarations config.challenge_module)).map
      ("owned: " ++ ·) ++
    (evidenced headlines evidence).map ("evidence: " ++ ·)
  unless project.check inventory && failures.isEmpty do
    throw <| IO.userError ("LeanEvidence audit failed:\n" ++ "\n".intercalate failures.toList)
  IO.println s!"Checked {inventory.modules.size} modules and {inventory.declarations.size} declarations"
  for line in headlines do
    let premises := "; ".intercalate (line.premises.map (describe evidence)).toList
    IO.println (s!"{if proved line.premises then "●" else "◕"} {line.name}" ++
      if premises.isEmpty then "" else s!"  ({premises})")
  IO.println s!"Owned: {" ".intercalate (← ownedFiles project inventory config.challenge_module).toList}"

end LeanEvidence.Audit
