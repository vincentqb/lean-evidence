module

public import Tests.Fixtures.Adapter
public meta import LeanEvidence.Commands

public section

namespace Tests.Fixtures.Rejected

open LeanEvidence

def uncovered (n : Nat) : Nat := n + 1

private unsafe def hiddenUnsafe (n : Nat) : Nat := n + 1

partial def diverging (n : Nat) : Nat := diverging n

abbrev Effect := IO Nat

def hiddenEffect : Effect := pure 0

structure EffectBox where
  action : IO Nat

def EffectBox.ofNat (n : Nat) : Nat := n + 1

def packagedEffect : EffectBox := ⟨pure 0⟩

initialize startup : Nat ← pure 0

@[extern "lean_nat_succ"] def unregistered (n : Nat) : Nat := n + 1

@[extern "lean_nat_pred"] def wrongSuccessor (n : Nat) : Nat := n + 1

axiom raw : False

theorem hole : False := by sorry

def spoof._unsafe_rec (n : Nat) : Nat := n + 1

structure Box (α : Type) where
  value : α

def Box.value._default {α : Type} (value : α) : α := value

def runtimeHelper (n : Nat) : Nat := n + 1

def redirected (n : Nat) : Nat := n + 1

ProvenTheorem redirected_contract : Contract redirected (fun f => ∀ n, n < f n) := by
  intro n
  exact Nat.lt_succ_self n

@[csimp] theorem redirect : @redirected = @Adapter.successor := by
  funext n
  rfl

end Tests.Fixtures.Rejected
