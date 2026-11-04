module

public meta import LeanEvidence.Basic

public section
namespace Tests.Assumptions

UnprovenConjecture input : 1 = 2

DerivedConjecture conditional : 1 = 2 := input

theorem raw_hole : 2 = 3 := by sorry

axiom external : 3 = 4
theorem external_chain : 3 = 4 := external

/-- Reference fixture: Lean native evaluation of 1 + 1, expected value 2.
Reproduce with the pinned Lean version and `lake test`. -/
ConformanceFixture native_fixture : 1 + 1 = 2

end Tests.Assumptions
