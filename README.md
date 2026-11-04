# LeanEvidence

Compiled architecture and evidence for **Lean 4.35.0**. `lake build` checks every
production module against a Lean `Project`, including private definitions,
initializers, `extern`, `implemented_by`, and `csimp` replacements.

The `core` is safe, total, and free of IO and initializers. Every public core
function needs a kernel-checked `Contract` naming its implementation.
Specifications remain the author's responsibility; the
[constant-folding example](Examples/ConstantFolding/Contracts.lean) proves behavior
against independent semantics.

Effects belong in `adapter` modules. A `foreign` binding requires a pure core model,
a universal `WorldClaim` of agreement, and a native `ConformanceFixture` comparing
the binding with that model. Elaboration and audit code belongs in `meta` tooling.

Add the dependency and audit target to `lakefile.lean`; use module globs so new
files are included automatically:

```lean
require lean_evidence from git
  "https://github.com/vincentqb/lean-evidence" @ "main"

lean_lib MyLib where
  globs := #[.one `MyLib, .submodules `MyLib]
lean_lib Scripts where
  globs := #[.submodules `Scripts]

@[default_target]
target audit pkg : Unit := do
  return (← pkg.toPackage.fetchFacetJob `leanEvidence).map (fun _ => ())
```

Declare every production module in `Scripts/Audit.lean`:

```lean
module
public meta import LeanEvidence
public section
meta section
open Lean LeanEvidence

def project : Project := {
  modules := #[⟨`MyLib, .core⟩, ⟨`Scripts.Audit, .tooling⟩]
  trusted := #[`Init, `Std, `Lean, `LeanEvidence]
}

def main (args : List String) : IO Unit :=
  Audit.run project (args.toArray.map String.toName)
```

Use `module`, `public`, and `import all` for explicit API boundaries, and disable
`autoImplicit` in the package's `leanOptions`. The shared Lake facet builds the
catalog and rejects missing or stale classifications.

`Policy.lean` defines the pure rules; `Contracts.lean` proves the checkers match
them. `Commands.lean`, `Audit.lean`, and `Report.lean` provide evidence authoring,
compiled inspection, and JSON. `Examples/` is the template; `Tests/` holds regression
tests and deliberately invalid fixtures.

The repository enforces its own policy and contracts:

```sh
lake build
lake test
```

`lake env lean --run path/to/Script.lean ...` checks a script and calls its `main`.
The audit receives its module arguments from Lake. Tooling is marked `meta`, and
Lean erases proofs from runtime code. Checker correctness is kernel-proved;
reflection, compiler correctness, and native execution remain trusted.
