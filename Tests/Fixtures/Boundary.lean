module

public section

namespace Tests.Fixtures

@[extern "lean_nat_succ"] opaque nativeSucc : @& Nat → Nat

@[extern "lean_nat_pred"] opaque wrongSucc : @& Nat → Nat

end Tests.Fixtures
