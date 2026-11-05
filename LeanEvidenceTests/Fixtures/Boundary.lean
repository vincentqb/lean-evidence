module

public section

namespace LeanEvidenceTests.Fixtures

@[extern "lean_nat_succ"] opaque nativeSucc : @& Nat → Nat

@[extern "lean_nat_pred"] opaque wrongSucc : @& Nat → Nat

end LeanEvidenceTests.Fixtures
