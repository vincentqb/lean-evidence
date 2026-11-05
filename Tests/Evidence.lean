module

meta import Tests.Support
import Tests.Assumptions
public meta import LeanEvidence.Commands

public section
namespace Tests.Evidence

theorem existing : ∀ n : Nat, n + 0 = n := by simp
ProvenTheorem existing_contract : ∀ n : Nat, n + 0 = n := existing
assert_evidence existing_contract is "ProvenTheorem"
rejects "Type mismatch" in ProvenTheorem wrong_existing : False := existing
assert_absent wrong_existing

def data : Nat := 1
rejects "proposition" in ProvenTheorem nonpropositional : Nat := data

theorem headline_proof : ∀ n : Nat, n + 0 = n := by simp
ProvenTheorem headline : ∀ n : Nat, n + 0 = n := headline_proof
assert_evidence headline is "ProvenTheorem"
rejects "Type mismatch" in ProvenTheorem mismatch : False := True.intro
rejects "Unknown identifier" in ProvenTheorem missing_proof : True := missing

rejects "nonstandard axioms" in
  ProvenTheorem input_as_proven : 1 = 2 := Tests.Assumptions.input
rejects "nonstandard axioms" in
  ProvenTheorem conditional_as_proven : 1 = 2 := Tests.Assumptions.conditional
rejects "nonstandard axioms" in
  ProvenTheorem hole_as_proven : 2 = 3 := Tests.Assumptions.raw_hole
rejects "nonstandard axioms" in
  ProvenTheorem axiom_as_proven : 3 = 4 := Tests.Assumptions.external_chain
rejects "nonstandard axioms" in
  ProvenTheorem fixture_as_proven : 1 + 1 = 2 := Tests.Assumptions.native_fixture
assert_evidence Tests.Assumptions.native_fixture is "ConformanceFixture"

theorem depth1 : 1 = 2 := Tests.Assumptions.input
theorem depth2 : 1 = 2 := depth1
theorem depth3 : 1 = 2 := depth2
theorem depth4 : 1 = 2 := depth3
theorem depth5 : 1 = 2 := depth4
rejects "nonstandard axioms" in ProvenTheorem deep_alias : 1 = 2 := depth5

DerivedConjecture conditional : 1 = 2 := Tests.Assumptions.conditional
assert_assumptions conditional = [Tests.Assumptions.input]

DerivedConjecture clean : ∀ n : Nat, n + 0 = n := existing
assert_assumptions clean = []

rejects "hidden body" in
  DerivedConjecture imported_hole : 2 = 3 := Tests.Assumptions.raw_hole
theorem local_hole_proof : 2 = 3 := by sorry
rejects "raw sorry" in DerivedConjecture local_hole : 2 = 3 := local_hole_proof
rejects "unregistered axiom" in
  DerivedConjecture raw_axiom : 3 = 4 := Tests.Assumptions.external_chain
rejects "Type mismatch" in DerivedConjecture clean_wrong : False := True.intro

Test samples : 1 + 1 = 2 := by decide
Test samples : 2 + 1 = 2 := by decide
Test samples : 3 + 1 = 2 := by exact unknown_proof
Test samples : 4 + 1 = 2 := by sorry
Test samples : 1 + 1 = 2 := Tests.Assumptions.native_fixture
assert_receipts samples = 1/5
assert_absent samples_test_2
assert_absent samples_test_3
assert_absent samples_test_4
assert_absent samples_test_5
rejects "Type mismatch" in Test nonpropositional_sample : Nat := 7
assert_absent nonpropositional_sample_case_1
rejects "1/5 tests passed" in TestedConjecture samples : ∀ n : Nat, n + 1 = 2
FailingConjecture samples : ∀ n : Nat, n + 1 = 2
assert_evidence samples is "FailingConjecture"
rejects "before declaring evidence" in Test samples : True := True.intro
assert_receipts samples = 1/5

Test passing_samples : 1 + 0 = 1 := by decide
Test passing_samples : 2 + 0 = 2 := by decide
assert_receipts passing_samples = 2/2
rejects "marked as `meta`" in
  def runtime_receipt : Bool := passing_samples_result_1
TestedConjecture passing_samples : ∀ n : Nat, n + 0 = n
assert_evidence passing_samples is "TestedConjecture"
rejects "before declaring evidence" in Test passing_samples : False := by decide
assert_receipts passing_samples = 2/2
rejects "nonstandard axioms" in
  ProvenTheorem samples_as_proven : ∀ n : Nat, n + 0 = n := passing_samples

Test unrelated_samples : 2 + 2 = 4 := by decide
rejects "test is not an instance" in
  TestedConjecture unrelated_samples : ∀ n : Nat, n + 1 = n
assert_absent unrelated_samples
assert_absent unrelated_samples_case_1_from_claim
assert_receipts unrelated_samples = 1/1

Test unrelated_failure : 2 + 2 = 5 := by decide
rejects "test is not an instance" in
  FailingConjecture unrelated_failure : ∀ n : Nat, n + 1 = n

rejects "use Test" in TestedConjecture empty : True
rejects "use Test" in FailingConjecture empty : True
Test passing : True := True.intro
rejects "no failing test" in FailingConjecture passing : True

rejects "doc comment" in Sketch undocumented
/-- The evaluator should expose a stable contract to its callers. -/
Sketch future
assert_evidence future is "Sketch"
rejects "marked as `meta`" in
  def runtime_sketch : Unit := future
rejects "doc comment" in WorldClaim undocumented_world := False

section
variable (foreign : Nat → Nat)

/-- The FFI returns n + 1 for input n. A differing reply falsifies this assumption. -/
WorldClaim intact := ∀ n : Nat, foreign n = n + 1
assert_evidence intact is "WorldClaim"
ProvenTheorem explicit_hypothesis : intact foreign → ∀ n : Nat, n < foreign n := by
  intro h n
  rw [h n]
  exact Nat.lt_succ_self n
rejects "Type mismatch" in
  ProvenTheorem world_as_fact : intact foreign := intact foreign
rejects "before declaring evidence" in Test explicit_hypothesis : True := True.intro
rejects "proposition" in ProvenTheorem world_value : Prop := intact foreign

end

UnitTest concrete : 3 + 4 = 7
assert_evidence concrete is "UnitTest"
rejects "false" in UnitTest assumed : 1 = 2
rejects "doc comment" in ConformanceFixture undocumented_fixture : 1 + 1 = 2

DerivedConjecture conditional_alias : 1 = 2 := conditional
assert_assumptions conditional_alias = [Tests.Assumptions.input]
DerivedConjecture tested_alias : ∀ n : Nat, n + 0 = n := passing_samples
assert_evidence tested_alias is "DerivedConjecture"
assert_assumptions tested_alias = [passing_samples]

Requirements ready where
  proof identity : ∀ n : Nat, n + 0 = n := headline
  proof derived : ∀ n : Nat, n + 0 = n := clean
  test addition : 3 + 4 = 7 := concrete

rejects "marked as `meta`" in
  def runtime_inventory : Array Lean.Name := ready

Requirements pending where
  proof identity : ∀ n : Nat, n + 0 = n := headline
  proof commutativity : ∀ a b : Nat, a + b = b + a
  test addition : 0 + 0 = 0

rejects "type mismatch" in
  Requirements wrong_statement where
    proof identity : ∀ n : Nat, 0 + n = n := headline
rejects "wrong evidence kind" in
  Requirements proof_as_test where
    test identity : ∀ n : Nat, n + 0 = n := headline
rejects "wrong evidence kind" in
  Requirements test_as_proof where
    proof addition : 3 + 4 = 7 := concrete
rejects "wrong evidence kind" in
  Requirements conjecture_as_proof where
    proof identity : ∀ n : Nat, n + 0 = n := passing_samples
rejects "wrong evidence kind" in
  Requirements assumption_as_proof where
    proof impossible : 1 = 2 := conditional
rejects "wrong evidence kind" in
  Requirements fixture_as_test where
    test addition : 1 + 1 = 2 := Tests.Assumptions.native_fixture
rejects "no registered evidence" in
  Requirements unregistered_proof where
    proof identity : ∀ n : Nat, n + 0 = n := existing
rejects "duplicate required claim" in
  Requirements duplicate where
    proof identity : ∀ n : Nat, n + 0 = n := headline
    proof identity : ∀ n : Nat, n + 0 = n := clean
rejects "at least one required claim" in Requirements empty_inventory where
rejects "proof or test" in
  Requirements invalid_kind where
    conjecture identity : ∀ n : Nat, n + 0 = n
rejects "type mismatch" in
  Requirements nonpropositional_inventory where
    proof data : Nat
rejects "nonstandard axioms" in
  Requirements assumed_statement where
    proof invalid : Eq.ndrec (motive := fun _ : Nat => Prop) (1 = 1) local_hole_proof

namespace Nested

ProvenTheorem _root_.Tests.Evidence.root_contract : True := True.intro
assert_evidence _root_.Tests.Evidence.root_contract is "ProvenTheorem"
Test _root_.Tests.Evidence.root_samples : True := True.intro
TestedConjecture _root_.Tests.Evidence.root_samples : True
assert_evidence _root_.Tests.Evidence.root_samples is "TestedConjecture"
assert_receipts _root_.Tests.Evidence.root_samples = 1/1

Requirements _root_.Tests.Evidence.root_inventory where
  proof identity : ∀ n : Nat, n + 0 = n := Tests.Evidence.headline

end Nested

end Tests.Evidence
