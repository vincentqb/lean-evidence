module

public import Examples.ConstantFolding.Shell

public section

namespace Examples.ConstantFolding

theorem fold_idempotent (normalizes : Normalizes fold) (e : Expr) : fold (fold e) = fold e :=
  fixed_of_normal (fold e) (normalizes e)

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e) := by
  simp only [Shell.output, evalNative_eq agrees, fold_preserves_meaning]

end Examples.ConstantFolding
