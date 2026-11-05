# LeanEvidence

Compiled architecture and required evidence for **Lean 4.35.0**. `lake build`
checks every production module, including private code and compiler replacements,
and verifies that each required proposition has its registered proof or test.

In `MyLib/Core.lean`, state requirements separately from their witnesses:

```lean
module
public meta import LeanEvidence
public section
namespace MyLib
open LeanEvidence

@[expose] def advance (n : Nat) : Nat := n + 1
ProvenTheorem advance_spec : Contract advance (fun f => ∀ n, n < f n) := by
  intro n
  exact Nat.lt_succ_self n
UnitTest advance_zero : advance 0 = 1

Requirements obligations where
  proof increasing : ∀ n : Nat, n < advance n := advance_spec
  test zero : advance 0 = 1 := advance_zero
end MyLib
```

Re-export it from `MyLib.lean`:

```lean
module
public import MyLib.Core
```

Omit `:= witness` to record an outstanding requirement. Completion, outstanding
claims, and the theorem index are derived from the selected compiled inventories.
Specifications remain the author's responsibility; the
[constant-folding example](Examples/ConstantFolding/Contracts.lean) uses independent semantics.

In `lakefile.lean`, add the dependency and shared audit facet:

```lean
require lean_evidence from git
  "https://github.com/vincentqb/lean-evidence" @ "main"

package my_lib where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib MyLib where
  globs := #[.one `MyLib, .submodules `MyLib]
lean_lib Scripts where
  globs := #[.submodules `Scripts]

@[default_target]
target audit pkg : Unit := do
  return (← pkg.toPackage.fetchFacetJob `leanEvidence).map (fun _ => ())
```

In `Scripts/Audit.lean`, classify every production module and select requirements:

```lean
module
public meta import LeanEvidence
public section
meta section
open Lean LeanEvidence

def project : Project := {
  modules := #[⟨`MyLib, .core⟩, ⟨`MyLib.Core, .core⟩, ⟨`Scripts.Audit, .tooling⟩]
  requirements := #[`MyLib.obligations]
  trusted := #[`Init, `Std, `Lean, `LeanEvidence]
}

def main (args : List String) : IO Unit :=
  Audit.run project (args.toArray.map String.toName)
```

The `core` is safe, total, and free of IO and initializers; public functions need
a kernel-checked `Contract`. Effects belong in `adapter` modules. A `foreign`
binding requires a pure model, a universal `WorldClaim` of agreement, and a native
`ConformanceFixture`. Tooling is `meta`. Use `module` and `public` for API boundaries,
and `import all` in proof modules that need private bodies. Import LeanEvidence with
`meta` to keep auditing, inventories, and test receipts out of runtime dependencies;
proofs erase. Programs that execute the policy checkers can import
`LeanEvidence.Policy` directly.

```sh
lake build
lake lint
lake test
```

Lake supplies the audit's module catalog. Run other scripts with
`lake env lean --run path/to/Script.lean ...`.

`LeanEvidence/` is the library, `Examples/` the template, and `Tests/` the regression
suite. This repository audits its own requirements and proves its policy checkers
and JSON fields correct. Reflection, compilation, and native execution remain trusted.
