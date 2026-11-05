module

public import Tests.Fixtures.Spec
public meta import LeanEvidence

public section

namespace Tests.Fixtures

inductive Tree where
  | leaf
  | fork : Tree → Tree → Tree
  deriving Repr

structure Box (α : Type) where
  value : Option α := none

def size : Tree → Nat
  | .leaf => 1
  | .fork l r => size l + size r

def halve (n : Nat) : Nat :=
  if h : n < 2 then 0 else halve (n - 2) + 1
termination_by n
decreasing_by omega

private def helper (n : Nat) : Nat := n

def identity (n : Nat) : Nat := helper n

def successor (n : Nat) : Nat := nativeSucc n

theorem successor_grows (agrees : SuccAgrees) (n : Nat) : n < successor n := by
  simp only [successor, agrees n]
  omega

theorem even_four : EvenFour := rfl

Test Identity identity : identity 3 = 3 := by decide

theorem uses_world (agrees : SuccAgrees) : successor 1 = 2 := agrees 1

theorem uses_open (h : Identity identity) : identity 5 = 5 := h 5

theorem uses_discharged (h : EvenFour) : 4 % 2 = 0 := h

theorem uses_unchecked (h : Unchecked) : wrongSucc 0 = 1 := h 0

end Tests.Fixtures
