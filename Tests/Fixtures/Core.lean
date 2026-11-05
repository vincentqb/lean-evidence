module

public meta import LeanEvidence.Commands

public section

namespace Tests.Fixtures.Core

open LeanEvidence

inductive Mode where
  | idle | active
  deriving BEq, DecidableEq, Repr

inductive Tree where
  | leaf
  | fork : Tree → Tree → Tree

structure Box (α : Type) where
  value : Option α := none

def successor (n : Nat) : Nat := n + 1

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + n + 1

ProvenTheorem successor_increases : Contract successor (fun f => ∀ n, n < f n) := by
  intro n
  exact Nat.lt_succ_self n

ProvenTheorem sumTo_bounds : Contract sumTo (fun f => ∀ n, n ≤ f n) := by
  intro n
  cases n <;> simp [sumTo] <;> omega

Requirements obligations where
  proof successor : Contract successor (fun f => ∀ n, n < f n) := successor_increases
  proof sum : Contract sumTo (fun f => ∀ n, n ≤ f n) := sumTo_bounds

end Tests.Fixtures.Core
