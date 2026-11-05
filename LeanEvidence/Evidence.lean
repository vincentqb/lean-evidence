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

structure Requirement (statement : Prop) where
  witness : Option (PLift statement) := none

@[expose] def Requirement.isComplete {statement : Prop} (r : Requirement statement) : Bool :=
  r.witness.isSome

inductive RequirementKind where
  | proof | test
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

structure ClaimFact where
  inventory : Name
  name : Name
  kind : RequirementKind
  evidence : Option Name := none
  verified : Bool := false
  deriving Inhabited, Repr

@[expose] def ClaimFact.isComplete (claim : ClaimFact) : Bool :=
  claim.verified && claim.evidence.isSome

namespace Claims

@[expose] def isComplete (inventories : Array Name) (claims : Array ClaimFact) : Bool :=
  !inventories.isEmpty &&
    decide inventories.toList.Nodup &&
    decide (claims.toList.map (·.name)).Nodup &&
    inventories.all (fun name => claims.any (·.inventory == name)) &&
    claims.all (fun claim => inventories.contains claim.inventory && claim.isComplete)

def Complete (inventories : Array Name) (claims : Array ClaimFact) : Prop :=
  inventories ≠ #[] ∧ inventories.toList.Nodup ∧
    (claims.toList.map (·.name)).Nodup ∧
    (∀ name ∈ inventories, ∃ claim ∈ claims, claim.inventory = name) ∧
    (∀ claim ∈ claims, claim.inventory ∈ inventories ∧ claim.verified = true ∧
      ∃ evidence, claim.evidence = some evidence)

@[expose] def outstanding (claims : Array ClaimFact) : Array Name :=
  (claims.filter (! ·.isComplete)).map (·.name)

end Claims

@[expose] def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

@[expose] def nonstandardAxioms (axioms : Array Name) : Array Name :=
  axioms.filter (!standardAxioms.contains ·)

end LeanEvidence
