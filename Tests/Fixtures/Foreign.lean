module

public import Tests.Fixtures.Core
public meta import Tests.Fixtures.Core
public meta import LeanEvidence.Commands

public section

namespace Tests.Fixtures.Foreign

open LeanEvidence

@[extern "lean_nat_succ"] def successor (n : Nat) : Nat := n + 1

private unsafe def replacement (n : Nat) : Nat := n + 1

@[implemented_by replacement] def replaced (n : Nat) : Nat := Core.successor n

/-- The runtime successor agrees with the Lean model for every input.
A returned value other than n + 1 falsifies this assumption. -/
WorldClaim successor_agrees := ∀ n, successor n = Core.successor n

/-- The compiled replacement agrees with the Lean model for every input.
A returned value other than n + 1 falsifies this assumption. -/
WorldClaim replacement_agrees := ∀ n, replaced n = Core.successor n

end Tests.Fixtures.Foreign
