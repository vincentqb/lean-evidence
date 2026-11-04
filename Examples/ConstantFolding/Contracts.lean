module

public import Examples.ConstantFolding.Defs
import all Examples.ConstantFolding.Defs
import Std.Tactic
public meta import LeanEvidence

public section

namespace Examples.ConstantFolding

ProvenTheorem eval_sound :
    LeanEvidence.Contract eval (fun evaluate =>
      ∀ (env : Nat → Nat) (e : Expr), Evaluates env e (evaluate env e)) :=
  by
    intro env e
    induction e with
    | lit n => exact .lit n
    | var x => exact .var x
    | add a b ha hb => exact .add ha hb

ProvenTheorem eval_complete :
    ∀ (env : Nat → Nat) (e : Expr) (v : Nat),
      Evaluates env e v → eval env e = v :=
  by
    intro env e v h
    induction h <;> simp_all [eval]

private theorem eval_combine (env : Nat → Nat) (a b : Expr) :
    eval env (combine a b) = eval env a + eval env b := by
  cases a <;> cases b <;> rfl

private theorem eval_fold (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e := by
  induction e <;> simp_all [fold, eval, eval_combine]

private theorem semantics_iff (env : Nat → Nat) (e : Expr) (v : Nat) :
    Evaluates env e v ↔ eval env e = v := by
  constructor
  · exact eval_complete env e v
  · intro h
    rw [← h]
    exact eval_sound env e

ProvenTheorem fold_preserves_meaning :
    LeanEvidence.Contract fold (fun optimize =>
    ∀ (env : Nat → Nat) (e : Expr) (v : Nat),
      Evaluates env (optimize e) v ↔ Evaluates env e v) :=
  by
    intro env e v
    rw [semantics_iff, semantics_iff, eval_fold]

ProvenTheorem fold_idempotent : ∀ (e : Expr), fold (fold e) = fold e :=
  by
    intro e
    induction e with
    | lit n => rfl
    | var x => rfl
    | add a b ha hb =>
      cases h₁ : fold a <;> cases h₂ : fold b <;> simp_all [fold, combine]

private theorem combine_size (a b : Expr) :
    nodeCount (combine a b) ≤ 1 + nodeCount a + nodeCount b := by
  cases a <;> cases b <;> simp [combine, nodeCount] <;> omega

ProvenTheorem fold_never_grows : LeanEvidence.Contract nodeCount (fun size =>
    ∀ (e : Expr), size (fold e) ≤ size e) :=
  by
    intro e
    induction e with
    | lit n => exact Nat.le_refl _
    | var x => exact Nat.le_refl _
    | add a b ha hb =>
      have h := combine_size (fold a) (fold b)
      simp only [fold, nodeCount]
      omega

UnitTest fold_nested_literals :
    fold (.add (.lit 2) (.add (.lit 3) (.lit 4))) = .lit 9

UnitTest fold_with_variable :
    fold (.add (.var 0) (.add (.lit 3) (.lit 4))) = .add (.var 0) (.lit 7)

end Examples.ConstantFolding
