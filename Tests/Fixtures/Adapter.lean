module

public import Tests.Fixtures.Foreign
public meta import Tests.Fixtures.Foreign
public meta import LeanEvidence.Commands

public section

namespace Tests.Fixtures.Foreign

open LeanEvidence

/-- Lean 4.35.0's lean_nat_succ, executed through native_decide on 0 and 41. -/
ConformanceFixture successor_cases :
  successor 0 = Core.successor 0 ∧ successor 41 = Core.successor 41

/-- The compiled implemented_by replacement, executed on 0 and 41. -/
ConformanceFixture replacement_cases :
  replaced 0 = Core.successor 0 ∧ replaced 41 = Core.successor 41

ForeignBinding successor models Core.successor assumes successor_agrees conforms successor_cases
ForeignBinding replaced models Core.successor assumes replacement_agrees conforms replacement_cases

end Tests.Fixtures.Foreign

namespace Tests.Fixtures.Adapter

open LeanEvidence

def advance (n : Nat) : IO Nat := pure (Foreign.successor n)

@[expose] def successor (n : Nat) : Nat := n + 1

ProvenTheorem foreign_successor_increases :
    Foreign.successor_agrees → ∀ n, n < Foreign.successor n := by
  intro agrees n
  rw [agrees n]
  exact Core.successor_increases n

end Tests.Fixtures.Adapter
