# LeanEvidence

Keep the claims you do not want to lose, for software written in **Lean 4.35.0**.
Headline theorems live in a protected `Manifest.lean`; `lake comparator` checks that the
implementation proves exactly those statements. Assumptions about the outside world and
unfinished claims are hypotheses of those theorems, so nothing uses `sorry` and the report
reads each headline's evidence from its type. `lake build` audits what Lean does not enforce.

| Role | Holds | Known correct by |
|---|---|---|
| `spec` | types, reference semantics, `WorldClaim`s, `Conjecture`s | you |
| `boundary` | `@[extern]` declarations only | assumptions, checked at build time |
| `core` | pure, total code: public interface, private helpers, proofs | kernel proofs |
| `shell` | IO glue; decisions belong in core | E2E tests |
| `tooling` | headline proofs, audits, scripts | never reached at runtime |

Lean's module system already keeps helpers private, hides unexposed bodies, and keeps
proofs and `meta` code out of binaries. The audit adds the rest: every module has a role,
runtime imports never leave spec/boundary/core for the shell, spec and core code has no
escape hatch (`partial`, `unsafe`, `@[extern]`, `@[implemented_by]`, initializers, IO,
`dbgTrace`), and only standard axioms appear. `layering_sound` in
[`LeanEvidence/Policy.lean`](LeanEvidence/Policy.lean) proves the per-module import rule
transitive: once the audit accepts, no runtime import chain leads from spec, boundary, or core
to the shell.

The [constant-folding template](Examples/ConstantFolding) shows each piece:

```lean
/-- The runtime's native addition agrees with `Nat.add`. A different sum for any pair
falsifies it. -/
WorldClaim NativeAddAgrees := ∀ a b, nativeAdd a b = a + b
Check NativeAddAgrees : nativeAdd (2 ^ 70) 1 = 2 ^ 70 + 1

Conjecture Normalizes (optimize : Expr → Expr) := ∀ e, normal (optimize e) = true
Test Normalizes fold : normal (fold (.add (.lit 1) (.lit 2))) = true := by decide

theorem output_correct (agrees : NativeAddAgrees) (e : Expr) :
    Shell.output e = toString (eval (fun _ => 0) e)
```

`Test` proves an instance in the kernel; `Check` compiles and runs it during the build,
including foreign code. Assumptions only a running system can exercise, such as system
calls, rest on live suites marked `@[exercises Claim]`; keep those suites in a default target
so the audit sees them. The audit reports each headline:

```text
◕ Examples.ConstantFolding.fold_idempotent  (open Examples.ConstantFolding.Normalizes [2 tests, 0 checks, 0 suites])
● Examples.ConstantFolding.output_correct  (world Examples.ConstantFolding.NativeAddAgrees [0 tests, 2 checks, 0 suites])
```

A headline is proved (●) when every premise is a world assumption or a proved conjecture.
Every world assumption needs a `Test`, `Check`, or live suite, and every hypothesis that
mentions no variable of the statement must be a claim, so no assumption hides as a plain `Prop`.

## Use it

```lean
require lean_evidence from git "https://github.com/vincentqb/lean-evidence" @ "main"

@[default_target]
target audit pkg : Unit := do
  return (← pkg.toPackage.fetchFacetJob `leanEvidence).map (fun _ => ())
```

`Scripts/Audit.lean` assigns roles by module prefix; the longest prefix wins:

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

`Manifest.lean` imports only spec modules, states each headline with `sorry`, and declares
the implementation functions it mentions as definition holes. `comparator.json` names the
headlines and holes; `Claims.lean`, a default target, proves them. Keep `Manifest` out of the
default targets, and make `Spec`, `Boundary`, `Manifest`,
`comparator.json`, `Scripts/Audit.lean`, `lakefile.lean`, and `lake-manifest.json` read-only
for agents.

```sh
lake build && lake test && lake comparator
```

`Check`s on foreign code compile the boundary natively (`precompileModules`). Where the
bundled clang cannot run, set `LEAN_CC` and build the challenge module before
`lake comparator`, whose sandbox then reuses the native artifacts. Use `lake check --paranoid`
in CI to replay the build through Lean's independent kernels.
