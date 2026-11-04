module

public meta import Lean

public section
meta section

open Lean

namespace LeanEvidence

inductive EvidenceKind where
  | proven | derived | unproven | tested | failing | sketch | world | unitTest | fixture
  deriving BEq, ReflBEq, LawfulBEq, Inhabited, Repr

instance : ToString EvidenceKind where
  toString
    | .proven => "ProvenTheorem"
    | .derived => "DerivedConjecture"
    | .unproven => "UnprovenConjecture"
    | .tested => "TestedConjecture"
    | .failing => "FailingConjecture"
    | .sketch => "Sketch"
    | .world => "WorldClaim"
    | .unitTest => "UnitTest"
    | .fixture => "ConformanceFixture"

def EvidenceKind.requiresProof : EvidenceKind → Bool
  | .proven | .unitTest => true
  | _ => false

structure Evidence where
  kind : EvidenceKind
  assumptions : Array Name := #[]
  ownHole : Bool := false
  deriving Inhabited, Repr

def Evidence.assumptionNames (e : Evidence) (n : Name) : Array Name :=
  if e.ownHole then #[n] else e.assumptions

def Evidence.isComplete (e : Evidence) : Bool :=
  e.kind.requiresProof || (e.kind == .derived && e.assumptions.isEmpty)

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

structure TestResults where
  passed : Nat := 0
  total : Nat := 0
  deriving Inhabited, Repr

def TestResults.ofResult (passed : Bool) : TestResults :=
  { passed := if passed then 1 else 0, total := 1 }

def TestResults.merge (a b : TestResults) : TestResults :=
  { passed := a.passed + b.passed, total := a.total + b.total }

def TestResults.verdict (r : TestResults) : Option EvidenceKind :=
  if r.total == 0 then none
  else some (if r.passed == r.total then .tested else .failing)

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

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def nonstandardAxioms (axioms : Array Name) : Array Name :=
  axioms.filter (!standardAxioms.contains ·)

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

end LeanEvidence
