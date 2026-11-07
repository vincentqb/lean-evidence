module

public import Examples.ConstantFolding.Shell

public section

namespace Examples.ConstantFolding

theorem fold_idempotent (normalizes : Normalizes fold) (e : Expr) : fold (fold e) = fold e :=
  fixed_of_normal (fold e) (normalizes e)

theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e) := by
  simp only [Shell.output, evalNative_eq agrees, fold_preserves_meaning]

theorem fold_preserves_meaning_rejects_constant :
    ¬ ∀ (env : Nat → Nat) (e : Expr), eval env ((fun _ => Expr.lit 0) e) = eval env e := by
  intro h
  exact absurd (h (fun _ => 0) (.lit 1)) (by decide)

theorem fold_closed_literal_rejects_identity :
    ¬ ∀ (e : Expr), closed e = true → ∃ n, id e = .lit n := by
  intro h
  obtain ⟨n, hn⟩ := h (.add (.lit 1) (.lit 2)) rfl
  cases hn

theorem fold_idempotent_rejects_bump :
    ¬ (Normalizes bump → ∀ e : Expr, bump (bump e) = bump e) := by
  intro h
  have := h (fun _ => rfl) (.lit 0)
  simp [bump, eval] at this

theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e)) := by
  intro h
  have := congrArg String.length (h (fun _ _ => rfl) (.lit 0))
  simp at this

end Examples.ConstantFolding
