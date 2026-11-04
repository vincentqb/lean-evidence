module

meta import Tests.Support
import Tests.Assumptions
public meta import LeanEvidence.WorldClaim

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

Test samples : 2 + 2 = 4 := by decide
Test samples : 2 + 2 = 5 := by decide
Test samples : True := by exact unknown_proof
Test samples : False := by sorry
Test samples : Nat := 7
Test samples : 1 + 1 = 2 := Tests.Assumptions.native_fixture
assert_receipts samples = 1/6
assert_absent samples_test_2
assert_absent samples_test_3
assert_absent samples_test_4
assert_absent samples_test_5
assert_absent samples_test_6
rejects "1/6 tests passed" in TestedConjecture samples : ∀ n : Nat, n + 1 = n
FailingConjecture samples : ∀ n : Nat, n + 1 = n
assert_evidence samples is "FailingConjecture"
rejects "before declaring evidence" in Test samples : True := True.intro
assert_receipts samples = 1/6

Test passing_samples : 1 + 0 = 1 := by decide
Test passing_samples : 2 + 0 = 2 := by decide
assert_receipts passing_samples = 2/2
TestedConjecture passing_samples : ∀ n : Nat, n + 0 = n
assert_evidence passing_samples is "TestedConjecture"
rejects "before declaring evidence" in Test passing_samples : False := by decide
assert_receipts passing_samples = 2/2
rejects "nonstandard axioms" in
  ProvenTheorem samples_as_proven : ∀ n : Nat, n + 0 = n := passing_samples

rejects "use Test" in TestedConjecture empty : True
rejects "use Test" in FailingConjecture empty : True
Test passing : True := True.intro
rejects "no failing test" in FailingConjecture passing : True

rejects "doc comment" in Sketch undocumented
/-- The evaluator should expose a stable contract to its callers. -/
Sketch future
assert_evidence future is "Sketch"
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

attribute [theorems headline clean] data
rejects "no registered evidence" in attribute [theorems headline_proof] data

/-- An entry with an authored scheduling dependency. -/
Sketch blocked
attribute [depends_on future headline, estimated_minutes 15, entry_point] blocked

namespace Nested

ProvenTheorem _root_.Tests.Evidence.root_contract : True := True.intro
assert_evidence _root_.Tests.Evidence.root_contract is "ProvenTheorem"
Test _root_.Tests.Evidence.root_samples : True := True.intro
TestedConjecture _root_.Tests.Evidence.root_samples : True
assert_evidence _root_.Tests.Evidence.root_samples is "TestedConjecture"
assert_receipts _root_.Tests.Evidence.root_samples = 1/1

end Nested

end Tests.Evidence
