module

public import Lean.Data.Name

public section

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

@[expose] def EvidenceKind.requiresProof : EvidenceKind → Bool
  | .proven | .unitTest => true
  | _ => false

structure Evidence where
  kind : EvidenceKind
  assumptions : Array Name := #[]
  ownHole : Bool := false
  deriving Inhabited, Repr

@[expose] def Evidence.assumptionNames (e : Evidence) (n : Name) : Array Name :=
  if e.ownHole then #[n] else e.assumptions

@[expose] def Evidence.isComplete (e : Evidence) : Bool :=
  e.kind.requiresProof || (e.kind == .derived && e.assumptions.isEmpty)

structure TestResults where
  passed : Nat := 0
  total : Nat := 0
  deriving Inhabited, Repr

@[expose] def TestResults.ofResult (passed : Bool) : TestResults :=
  { passed := if passed then 1 else 0, total := 1 }

@[expose] def TestResults.merge (a b : TestResults) : TestResults :=
  { passed := a.passed + b.passed, total := a.total + b.total }

@[expose] def TestResults.verdict (r : TestResults) : Option EvidenceKind :=
  if r.total == 0 then none
  else some (if r.passed == r.total then .tested else .failing)

@[expose] def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

@[expose] def nonstandardAxioms (axioms : Array Name) : Array Name :=
  axioms.filter (!standardAxioms.contains ·)

end LeanEvidence
