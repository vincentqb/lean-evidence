module

public meta import LeanEvidence.Evidence

public section
meta section

open Lean Elab Command

namespace LeanEvidence

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
  checkedCommand (← `(public theorem $n : $t := by native_decide))
  let name ← fullName n
  mark name .fixture
  attachDoc doc? name

end LeanEvidence
