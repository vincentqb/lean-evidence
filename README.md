# LeanEvidence

For software written in **Lean 4.35.0**: state the theorems you never want to lose in files
agents cannot edit, and let the build check that the code still proves them and that the
proofs cover the code that runs.

## Files

| File | Contains | Edited by |
|---|---|---|
| `MyApp/Spec.lean` | types, reference definitions, and the claims headlines rest on | you |
| `MyApp/Boundary.lean` | `@[extern]` declarations for foreign code | you |
| `MyApp/Core/…` | pure code: public interface, private helpers, and their proofs | agents |
| `MyApp/Shell.lean` | IO that connects the core to the world | agents |
| `Manifest.lean` | headline theorems, stated with `sorry` | you |
| `Claims.lean` | proofs of the headline theorems | agents |
| `comparator.json` | the headlines and the functions they constrain | you |
| `Scripts/Audit.lean` | the role of each module prefix | you |

Headlines are end-to-end theorems: they say what the program does in terms of the spec,
assuming only named claims. In the [template](Examples/ConstantFolding), `output_correct`
says the shell prints the true value of an expression, assuming native addition is correct.

## Syntax

```lean
/-- The runtime's native addition agrees with `Nat.add`. A different sum for any pair
falsifies it. -/
WorldClaim NativeAddAgrees := ∀ a b, nativeAdd a b = a + b
Check NativeAddAgrees : nativeAdd (2 ^ 70) 1 = 2 ^ 70 + 1
@[exercises NativeAddAgrees] def nativeAddSuite : IO Unit := ...

Conjecture Normalizes (optimize : Expr → Expr) := ∀ e, normal (optimize e) = true
Test Normalizes fold : normal (fold (.add (.add (.lit 1) (.lit 2)) (.lit 3))) = true := by decide

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e)
```

- `WorldClaim Name := P` names an assumption about the world; its doc comment names the
  observation that would falsify it.
- `Check Claim : instance` runs one instance of a claim during the build, foreign code included.
- `@[exercises Claim]` marks a live suite that exercises a claim while the program runs.
- `Conjecture Name := P` names a claim not yet proved; a theorem of type `Name` discharges it.
- `Test Claim : instance := proof` proves one instance of a claim in the kernel.
- A headline takes the claims it rests on as hypotheses; `lake build` reports it proved (●)
  once its conjectures are proved and derived (◕) until then.

Claims live in spec modules, and every world assumption a headline uses needs a `Check`,
suite, or `Test`.

## Setup

In `lakefile.lean`:

```lean
require lean_evidence from git "https://github.com/vincentqb/lean-evidence" @ "main"

@[default_target]
target audit pkg : Unit := do
  return (← pkg.toPackage.fetchFacetJob `leanEvidence).map (fun _ => ())
```

In `Scripts/Audit.lean`, the longest matching prefix gives each module its role:

```lean
module
public meta import LeanEvidence.Audit
public section
meta section
open LeanEvidence

def main (args : List String) : IO Unit :=
  Audit.run {
    layers := #[(`MyApp, .tooling), (`MyApp.Spec, .spec), (`MyApp.Boundary, .boundary),
      (`MyApp.Core, .core), (`MyApp.Shell, .shell)]
  } (args.toArray.map String.toName)
```

- `.spec` and `.boundary` modules hold what you own; boundary code is `@[extern]` only.
- `.core` code is pure and total: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`,
  initializers, IO, or `dbg*`.
- `.shell` code may do IO but reaches foreign code only through the boundary.
- `.tooling` covers proofs and scripts, which runtime code never imports.

`Manifest.lean` imports only spec modules, states each headline with `sorry`, and declares
each function a headline mentions as a hole, `def name : Type := sorry`; `comparator.json`
lists the headlines and holes. Keep `Manifest` out of the default targets.

## Run

```sh
lake build        # audit and headline report
lake test         # your tests, including the live suites
lake comparator   # Claims.lean proves exactly the statements in Manifest.lean
```

Make the files you own read-only for agents, along with `lakefile.lean` and
`lake-manifest.json`. `Check` on foreign code needs `precompileModules`; where the bundled
clang cannot run, set `LEAN_CC` and build the manifest before `lake comparator`. Use
`lake check --paranoid` in CI.
