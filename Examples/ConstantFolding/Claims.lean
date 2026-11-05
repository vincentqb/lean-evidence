module

public import Examples.ConstantFolding.Shell

public section

namespace Examples.ConstantFolding

theorem fold_preserves_meaning (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e :=
  eval_fold env e

theorem fold_closed_literal (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n :=
  closed_folds e h

theorem fold_idempotent (normalizes : Normalizes fold) (e : Expr) : fold (fold e) = fold e :=
  fixed_of_normal (fold e) (normalizes e)

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e) := by
  simp only [Shell.output, evalNative_eq agrees, eval_fold]

end Examples.ConstantFolding
