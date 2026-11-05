module

public import Tests.Fixtures.Boundary
meta import Tests.Fixtures.Boundary
public meta import LeanEvidence

public section

namespace Tests.Fixtures

/-- The native successor returns n + 1. Any other result falsifies it. -/
WorldClaim SuccAgrees := ∀ n, nativeSucc n = n + 1

Check SuccAgrees : nativeSucc 41 = 41 + 1

/-- An assumption nothing checks. Any use of it falsifies the audit. -/
WorldClaim Unchecked := ∀ n, wrongSucc n = n + 1

/-- `f` is the identity. -/
Conjecture Identity (f : Nat → Nat) := ∀ n, f n = n

Conjecture EvenFour := 4 % 2 = 0

inductive Mode where
  | idle | active
  deriving BEq, DecidableEq, Repr

end Tests.Fixtures
