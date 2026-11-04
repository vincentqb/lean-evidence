module

public meta import LeanEvidence.Evidence
public meta import LeanEvidence.Policy
public meta import Lean

public section
meta section

open Lean Elab Command

namespace LeanEvidence

initialize evidenceExt : SimplePersistentEnvExtension (Name × Evidence)
    (Std.HashMap Name Evidence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, e) => m.insert n e
    addImportedFn := fun entries => Id.run do
      let mut m := {}
      for a in entries do
        for (n, e) in a do m := m.insert n e
      return m
  }

def getEvidence? (env : Environment) (n : Name) : Option Evidence :=
  (evidenceExt.getState env)[n]?

initialize testResultsExt : SimplePersistentEnvExtension (Name × TestResults)
    (Std.HashMap Name TestResults) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, r) =>
      let p := (m[n]?).getD {}
      m.insert n (p.merge r)
    addImportedFn := fun entries => Id.run do
      let mut m : Std.HashMap Name TestResults := {}
      for a in entries do
        for (n, r) in a do
          let p := (m[n]?).getD {}
          m := m.insert n (p.merge r)
      return m
  }

def getTestResults (env : Environment) (n : Name) : Option TestResults :=
  (testResultsExt.getState env)[n]?

def unexpectedAxioms (n : Name) : CoreM (Array Name) := do
  return nonstandardAxioms (← collectAxioms n)

def requireProof (n : Name) : CoreM Unit := do
  let axioms ← unexpectedAxioms n
  unless axioms.isEmpty do
    throwError "{n} depends on nonstandard axioms: {axioms}. A proved entry may use only propext, Classical.choice, and Quot.sound."

def namedAssumptions (root : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let axioms ← unexpectedAxioms root
  for ax in axioms do
    unless ax == ``sorryAx do
      throwError "{root} depends on an unregistered axiom: {ax}"
  let mut todo := #[root]
  let mut visited : NameSet := {}
  let mut frontier : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (← unexpectedAxioms n).isEmpty then continue
    if let some e := getEvidence? env n then
      let assumptions := e.assumptionNames n
      if !assumptions.isEmpty then
        for dep in assumptions do
          if !frontier.contains dep then frontier := frontier.push dep
        continue
    let some info := env.find? n
      | throwError "Cannot inspect the assumed dependency {n}"
    let deps := info.getUsedConstantsAsSet
    if deps.contains ``sorryAx then
      throwError "{root} uses raw sorry in {n}; register the named assumption."
    unless (info.value? (allowOpaque := true)).isSome do
      throwError "Cannot name assumptions behind the hidden body of {n}. Use import all for this package's proof module."
    for dep in deps.toArray do todo := todo.push dep
  if !axioms.isEmpty && frontier.isEmpty then
    throwError "Cannot recover the named assumptions of {root}"
  return frontier.qsort (fun a b => a.toString < b.toString)

initialize contractExt : SimplePersistentEnvExtension (Name × Name)
    (Std.HashMap Name (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (implementation, proof) =>
      m.insert implementation ((m[implementation]?).getD #[] |>.push proof)
    addImportedFn := fun entries => Id.run do
      let mut m : Std.HashMap Name (Array Name) := {}
      for a in entries do
        for (implementation, proof) in a do
          m := m.insert implementation ((m[implementation]?).getD #[] |>.push proof)
      return m
  }

def getContracts (env : Environment) (implementation : Name) : Array Name :=
  (contractExt.getState env)[implementation]?.getD #[]

structure ForeignEvidence where
  binding : Name
  model : Name
  assumption : Name
  fixture : Name
  deriving Inhabited, Repr

initialize foreignExt : SimplePersistentEnvExtension ForeignEvidence
    (Std.HashMap Name ForeignEvidence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m entry => m.insert entry.binding entry
    addImportedFn := fun entries => Id.run do
      let mut m := {}
      for a in entries do
        for entry in a do m := m.insert entry.binding entry
      return m
  }

def getForeignEvidence? (env : Environment) (binding : Name) : Option ForeignEvidence :=
  (foreignExt.getState env)[binding]?

initialize runtimeAxiomExt : SimplePersistentEnvExtension (Name × Name)
    (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (axiomName, fixture) => m.insert axiomName fixture
    addImportedFn := fun entries => Id.run do
      let mut m := {}
      for a in entries do
        for (axiomName, fixture) in a do m := m.insert axiomName fixture
      return m
  }

def getRuntimeAxiomOrigin? (env : Environment) (axiomName : Name) : Option Name :=
  (runtimeAxiomExt.getState env)[axiomName]?

namespace Internal

def fullName (n : TSyntax `ident) : CommandElabM Name := do
  let name := n.getId
  let ns ← getCurrNamespace
  return if rootNamespace.isPrefixOf name then name.replacePrefix rootNamespace .anonymous
    else ns ++ name

def checkedCommand (cmd : Syntax) : CommandElabM Unit := do
  let before := (← get).messages.toList.filter (·.severity == .error) |>.length
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    elabCommand cmd
  let after := (← get).messages.toList.filter (·.severity == .error) |>.length
  if after > before then throwError "declaration failed to elaborate"

def attachDoc (doc? : Option (TSyntax `Lean.Parser.Command.docComment))
    (n : Name) : CommandElabM Unit := do
  if let some doc := doc? then
    liftTermElabM <| addDocString n Syntax.missing doc

def mark (n : Name) (kind : EvidenceKind) (assumptions : Array Name := #[])
    (ownHole : Bool := false) : CommandElabM Unit := do
  modifyEnv fun env => evidenceExt.addEntry env (n, { kind, assumptions, ownHole })

end Internal

open Internal

private def requireProp (n : Name) : CommandElabM Unit := do
  let info ← getConstInfo n
  let yes ← liftTermElabM <| Meta.isProp info.type
  unless yes do throwError "{n}: evidence must be a proof of a proposition"

private def registerContract (proof : Name) : CommandElabM Unit := do
  let type := (← getConstInfo proof).type
  unless type.getAppFn.constName? == some ``Contract do return
  let args := type.getAppArgs
  let some implementation := args[1]?.bind Expr.constName?
    | throwError "{proof}: Contract must name the implementation directly"
  modifyEnv fun env => contractExt.addEntry env (implementation, proof)

elab "Test " n:ident " : " t:term " := " body:term : command => do
  let name ← fullName n
  if (getEvidence? (← getEnv) name).isSome then
    throwError "{name}: use Test before declaring evidence"
  let results := (getTestResults (← getEnv) name).getD {}
  let witness := mkIdent (n.getId.appendAfter s!"_test_{results.total + 1}")
  let saved ← get
  let mut passed := false
  try
    checkedCommand (← `(public theorem $witness : $t := $body))
    let w ← resolveGlobalConstNoOverload witness
    requireProp w
    liftCoreM <| requireProof w
    passed := true
  catch _ =>
    set saved
  let receipt := mkIdent (n.getId.appendAfter s!"_result_{results.total + 1}")
  if passed then
    checkedCommand (← `(public def $receipt : Bool := true))
  else
    checkedCommand (← `(public def $receipt : Bool := false))
    logWarning m!"Test {name} [{results.total + 1}]: failed"
  modifyEnv fun env => testResultsExt.addEntry env (name, TestResults.ofResult passed)

elab doc?:(docComment)? "ProvenTheorem " n:ident " : " t:term " := " proof:term :
    command => do
  checkedCommand (← `(public theorem $n : $t := $proof))
  let name ← fullName n
  requireProp name
  liftCoreM <| requireProof name
  mark name .proven
  registerContract name
  attachDoc doc? name

private def conjecture (doc? : Option (TSyntax `Lean.Parser.Command.docComment))
    (n : TSyntax `ident) (t : TSyntax `term) (kind : EvidenceKind) : CommandElabM Unit := do
  let name ← fullName n
  if (← getEnv).contains name then throwError "{name} already exists; change its declaration to change evidence"
  checkedCommand (← `(public theorem $n : $t := by sorry))
  requireProp name
  mark name kind #[] true
  attachDoc doc? name

elab doc?:(docComment)? "UnprovenConjecture " n:ident " : " t:term : command =>
  conjecture doc? n t .unproven

private def testCounts (n : TSyntax `ident) : CommandElabM TestResults := do
  let name ← fullName n
  let some results := getTestResults (← getEnv) name
    | throwError "{name}: use Test before declaring test evidence"
  if results.verdict.isNone then throwError "{name}: at least one test is required"
  return results

elab doc?:(docComment)? "TestedConjecture " n:ident " : " t:term : command => do
  let r ← testCounts n
  if r.verdict != some .tested then throwError "{n}: {r.passed}/{r.total} tests passed"
  conjecture doc? n t .tested

elab doc?:(docComment)? "FailingConjecture " n:ident " : " t:term : command => do
  let r ← testCounts n
  if r.verdict != some .failing then throwError "{n}: no failing test was recorded"
  conjecture doc? n t .failing

elab doc?:(docComment)? "DerivedConjecture " n:ident " : " t:term " := " proof:term :
    command => do
  checkedCommand (← `(public theorem $n : $t := $proof))
  let name ← fullName n
  requireProp name
  let assumptions ← liftCoreM <| namedAssumptions name
  mark name .derived assumptions
  attachDoc doc? name
  if !assumptions.isEmpty then logInfo m!"{name}: assumes {assumptions}"

elab doc?:(docComment)? "Sketch " n:ident : command => do
  unless doc?.isSome do throwError "Sketch {n} requires a doc comment describing the future claim"
  checkedCommand (← `(public def $n : Unit := ()))
  let name ← fullName n
  mark name .sketch
  attachDoc doc? name

elab doc?:(docComment)? "WorldClaim " n:ident " := " t:term : command => do
  unless doc?.isSome do
    throwError "WorldClaim {n} requires a doc comment describing the assumption and a falsifying observation"
  checkedCommand (← `(@[expose] public def $n : Prop := $t))
  let name ← fullName n
  mark name .world
  attachDoc doc? name

elab doc?:(docComment)? "UnitTest " n:ident " : " t:term : command => do
  checkedCommand (← `(public theorem $n : $t := by decide))
  let name ← fullName n
  liftCoreM <| requireProof name
  mark name .unitTest
  attachDoc doc? name

elab doc?:(docComment)? "ConformanceFixture " n:ident " : " t:term : command => do
  unless doc?.isSome do throwError "ConformanceFixture {n} requires reference provenance in a doc comment"
  let before ← getEnv
  checkedCommand (← `(public theorem $n : $t := by native_decide))
  let name ← fullName n
  for ax in ← liftCoreM <| unexpectedAxioms name do
    unless !before.contains ax && (← getConstInfo ax).isAxiom do
      throwError "{name}: conformance fixture depends on an existing nonstandard axiom: {ax}"
    modifyEnv fun env => runtimeAxiomExt.addEntry env (ax, name)
  mark name .fixture
  attachDoc doc? name

private def agreement (binding model : Name) : MetaM Expr := do
  let binding ← Meta.mkConstWithFreshMVarLevels binding
  let model ← Meta.mkConstWithFreshMVarLevels model
  let type ← Meta.inferType binding
  unless ← Meta.isDefEq type (← Meta.inferType model) do
    throwError "the Lean model must have the same type"
  Meta.forallTelescope type fun arguments _ => do
    Meta.mkForallFVars arguments (← Meta.mkEq (mkAppN binding arguments) (mkAppN model arguments))

private def comparison (binding model : Name) (type : Expr) : MetaM Bool := do
  unless type.isAppOfArity ``Eq 3 do return false
  let lhs := type.getAppArgs[1]!
  let rhs := type.getAppArgs[2]!
  unless lhs.getAppFn.constName? == some binding &&
      rhs.getAppFn.constName? == some model do return false
  let leftArgs := lhs.getAppArgs
  let rightArgs := rhs.getAppArgs
  unless leftArgs.size == rightArgs.size do return false
  for (left, right) in leftArgs.zip rightArgs do
    unless ← Meta.isDefEq left right do return false
  return true

private partial def comparisonFixture (binding model : Name) (type : Expr) : MetaM Bool := do
  if type.isAppOfArity ``And 2 then
    return (← comparisonFixture binding model type.getAppArgs[0]!) &&
      (← comparisonFixture binding model type.getAppArgs[1]!)
  comparison binding model type

elab "ForeignBinding " binding:ident " models " model:ident
    " assumes " assumption:ident " conforms " fixture:ident : command => do
  let binding ← resolveGlobalConstNoOverload binding
  let model ← resolveGlobalConstNoOverload model
  let assumption ← resolveGlobalConstNoOverload assumption
  let fixture ← resolveGlobalConstNoOverload fixture
  let env ← getEnv
  unless isExtern env binding || (Compiler.getImplementedBy? env binding).isSome do
    throwError "{binding}: ForeignBinding requires extern or implemented_by"
  unless (getEvidence? env assumption).map (·.kind) == some .world do
    throwError "{assumption}: ForeignBinding requires a WorldClaim"
  unless (getEvidence? env fixture).map (·.kind) == some .fixture do
    throwError "{fixture}: ForeignBinding requires a ConformanceFixture"
  let some world := (← getConstInfo assumption).value?
    | throwError "{assumption}: WorldClaim body is unavailable"
  let agrees ← liftTermElabM <| Meta.forallTelescope world fun _ body => do
    return (← comparison binding model body) &&
      (← Meta.isDefEq world (← agreement binding model))
  unless agrees do
    throwError "{binding}: WorldClaim must state pointwise equality with the Lean model"
  unless ← liftTermElabM <| comparisonFixture binding model (← getConstInfo fixture).type do
    throwError "{binding}: fixture must compare the binding and model on the same inputs"
  unless (getForeignEvidence? env binding).isNone do
    throwError "{binding}: foreign evidence is already registered"
  modifyEnv fun env => foreignExt.addEntry env { binding, model, assumption, fixture }

end LeanEvidence
