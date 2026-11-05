module

public import LeanEvidenceTests.Fixtures.Boundary
meta import LeanEvidenceTests.Fixtures.Boundary
public meta import LeanEvidence

public section

namespace LeanEvidenceTests.Fixtures

/-- The native successor returns n + 1. Any other result falsifies it. -/
WorldClaim SuccAgrees := ∀ n, nativeSucc n = n + 1

Check SuccAgrees : nativeSucc 41 = 41 + 1

/-- An assumption nothing checks. Any use of it falsifies the audit. -/
WorldClaim Unchecked := ∀ n, wrongSucc n = n + 1

/-- The clock never runs backwards. A reading below an earlier one falsifies it. -/
WorldClaim ClockAdvances (now : Nat → Nat) := ∀ t, t ≤ now t

Conjecture Identity (f : Nat → Nat) := ∀ n, f n = n

Conjecture EvenFour := 4 % 2 = 0

end LeanEvidenceTests.Fixtures
