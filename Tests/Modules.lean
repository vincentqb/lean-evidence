module

meta import Tests.Support
public import Examples.ConstantFolding.Claims

public section

namespace Tests.Modules

open Examples.ConstantFolding

example (env : Nat → Nat) (e : Expr) : eval env (fold e) = eval env e :=
  fold_preserves_meaning env e

example (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e) :=
  output_correct agrees e

rejects "Unknown identifier" in #check Examples.ConstantFolding.combine
rejects "rfl" in theorem cannot_unfold : fold (.lit 4) = .lit 4 := by rfl
rejects "Type mismatch" in theorem world_is_not_a_fact : NativeAddAgrees := fun _ _ => rfl

end Tests.Modules
