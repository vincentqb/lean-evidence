module

meta import Tests.Support
public import Examples.ConstantFolding.Manifest

public section
namespace Tests.Modules
open Examples.ConstantFolding

example (env : Nat → Nat) (e : Expr) (v : Nat) :
    Evaluates env (fold e) v ↔ Evaluates env e v :=
  fold_preserves_meaning env e v

example (e : Expr) : fold (fold e) = fold e := fold_idempotent e

example : Expr → Expr := fold
rejects "Unknown identifier" in #check Examples.ConstantFolding.combine
rejects "Unknown identifier" in #check Examples.ConstantFolding.eval_fold
rejects "rfl" in theorem cannot_unfold : eval (fun _ => 0) (.lit 4) = 4 := by rfl

meta section
open LeanManifests

example (r : TestResults) :
    r.verdict = some .tested ↔ 0 < r.total ∧ r.passed = r.total :=
  Contracts.tested_iff r

example (e : Evidence) : e.needsWork = true → e.isComplete = false :=
  Contracts.unfinished_incomplete e

end

end Tests.Modules
