# LeanEvidence

For software written in **Lean 4.35.0**: state the theorems you never want to lose in files
agents cannot edit; `lake comparator` checks that the code still proves them, and
`lake build` checks that the code they constrain is the code that runs.

## Files

| File | Contains | Edited by |
|---|---|---|
| `MyApp/Spec.lean` | types, reference definitions, and the claims headlines rest on | you |
| `MyApp/Boundary.lean` | `@[extern]` declarations for foreign code | you |
| `MyApp/Core/…` | pure code: public interface, private helpers, and their proofs | agents |
| `MyApp/Shell.lean` | IO that connects the core to the world | agents |
| `Manifest.lean` | headline theorems, stated with `sorry` | you |
| `MyApp/Claims.lean` | proofs of the headline theorems | agents |
| `comparator.json` | the headlines and the functions they constrain | you |
| `Audit.lean` | the role of each module prefix | you |

Headlines are end-to-end theorems: they say what the program does in terms of the spec,
assuming only named claims. In the [template](Examples/ConstantFolding), `output_correct`
says the shell prints the true value of an expression, assuming native addition is correct.

## Syntax

```lean
public meta import LeanEvidence

/-- The runtime's native addition agrees with `Nat.add`. A different sum for any pair
falsifies it. -/
WorldClaim NativeAddAgrees := ∀ a b, nativeAdd a b = a + b
Check NativeAddAgrees : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71
@[exercises NativeAddAgrees] def nativeAddSuite : IO Unit := ...

Conjecture Normalizes (optimize : Expr → Expr) := ∀ e, normal (optimize e) = true
Test Normalizes fold : normal (fold (.add (.add (.lit 1) (.lit 2)) (.var 0))) = true := by decide

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e)
```

- `WorldClaim Name := P` names an assumption about the world; its doc comment names the
  observation that would falsify it.
- `Check Claim : instance` runs one instance of a claim during the build, foreign code included.
- `@[exercises Claim]` marks a live suite in a shell module that exercises a claim.
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
  return (← pkg.fetchFacetJob `leanEvidence).map (fun _ => ())
```

In `Audit.lean`, the longest matching prefix gives each module its role:

```lean
module
public meta import LeanEvidence.Audit

public meta def main : List String → IO Unit := LeanEvidence.Audit.run {
  layers := #[(`MyApp, .tooling), (`MyApp.Spec, .spec), (`MyApp.Boundary, .boundary),
    (`MyApp.Core, .core), (`MyApp.Shell, .shell)] }
```

- `.spec` and `.core` code is pure: no `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`,
  initializers, IO, or `dbg*`.
- `.boundary` code is `@[extern]` declarations only.
- `.shell` code may do IO but not `unsafe`, `@[extern]`, or `@[implemented_by]`.
- `.tooling` covers `Claims` and scripts; like every role, it may use only standard axioms.
- Non-`meta` imports run from tooling to shell to core to spec and boundary, never back;
  other libraries must be listed in `trusted`, which defaults to `Init`, `Std`, and `Lean`.

`Manifest.lean` imports only spec and boundary modules and declares each core or shell
function a headline mentions as a hole with the code's exact type, `def name : T := sorry`;
[`comparator.json`](comparator.json) lists the headlines and holes. Put `Claims` in a
default target, and declare `Manifest` as a `lean_lib` that is not one. The audit imports
every module of the default targets into one environment, so only one of them may define
`main`.

## Run

```sh
lake build        # audit and headline report
lake test         # your tests, including the live suites
lake comparator   # MyApp/Claims.lean proves exactly the statements in Manifest.lean
```

The audit reruns and prints its report only when a module, `Audit.lean`, `comparator.json`, or
`Manifest.lean` changes; `.lake/build/leanEvidence.txt` keeps the last report.

Make the files you own read-only for agents, along with `lakefile.lean` and
`lake-manifest.json`. `Check` on foreign code needs `precompileModules`. `lake comparator`
replays the headline proofs through the kernel in a separate process, which rejects proofs
that skipped the kernel during the build.
