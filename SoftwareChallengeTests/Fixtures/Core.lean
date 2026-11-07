module

public import SoftwareChallengeTests.Fixtures.Spec
public meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

inductive Tree where
  | leaf
  | fork : Tree → Tree → Tree
  deriving Repr

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

theorem uses_open (h : Identity identity) : identity 5 = 5 := h 5

theorem uses_discharged (h : EvenFour) : 4 % 2 = 0 := h

theorem uses_unchecked (h : Unchecked) : wrongSucc 0 = 1 := h 0

theorem uses_live (now : Nat → Nat) (h : ClockAdvances now) (t : Nat) : t ≤ now t := h t

theorem bounded (n : Nat) (h : n < 5) : n < 6 := by omega

theorem identity_fixed (n : Nat) : identity n = n := by simp [identity, helper]

theorem identity_fixed_rejects_successor : ¬ ∀ n : Nat, (fun n => n + 1) n = n := by
  intro h
  exact absurd (h 0) (by decide)

theorem mismatched_negation : ¬ ∀ n : Nat, n = n + 1 := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_three : identity 3 = 3 := by simp [identity, helper]

theorem identity_three_rejects_successor : ¬ (fun n : Nat => n + 1) 3 = 3 := by decide

theorem uses_unnamed (h : 1 = 2) : 1 = 2 := h

Conjecture CoreClaim := 1 = 1

end SoftwareChallengeTests.Fixtures
