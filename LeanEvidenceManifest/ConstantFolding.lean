module

public import Examples.ConstantFolding.Spec

public section

/-!
# Constant folding

Folding preserves meaning, removes every constant subexpression of a closed expression,
and the printed result is the true value. Not claimed: optimality for expressions with
variables beyond one pass, or anything about the native adder beyond `NativeAddAgrees`.
-/

namespace Examples.ConstantFolding

@[expose] def fold : Expr → Expr := sorry

@[expose] def Shell.output (e : Expr) : String := sorry

theorem fold_preserves_meaning (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e := by
  sorry

theorem fold_closed_literal (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n := by
  sorry

theorem fold_idempotent (normalizes : Normalizes fold) (e : Expr) : fold (fold e) = fold e := by
  sorry

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e) := by
  sorry

end Examples.ConstantFolding
