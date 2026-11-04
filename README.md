# LeanEvidence

Compiled claim inventories for Lean libraries. Use this package as a Lake
dependency and `meta import LeanEvidence` for the commands and evidence tracking.
Checks run during elaboration; Lean erases proposition proofs from executable code.

```lean
require lean_evidence from git
  "https://github.com/vincentqb/lean-evidence" @ "main"
```

Targets **Lean 4.35.0** only. Import `LeanEvidence.Tools` separately for JSON
reports, API indexes, work inventories, and LaTeX marker checks.

`Foo/Bar.lean` defines module `Foo.Bar`. Root files assemble the public imports;
`lakefile.lean` configures Lake.

| Path | Role |
| --- | --- |
| `LeanEvidence.lean` | Public library entry point |
| `LeanEvidence/` | Library implementation and its `Contracts/` proofs |
| `Examples/` | Compiled usage template |
| `Tests/` | Regression suite |
| `Scripts/` | Runnable tools with `main` |

The [compiled example](Examples/ConstantFolding/Contracts.lean) is the template:
[Defs](Examples/ConstantFolding/Defs.lean) defines the API and independent semantics,
and `Contracts` proves five universal properties and checks two finite cases.
Lean's `module`, `public`, and `import all` export contract types while keeping
implementation and proof bodies private.

`ProvenTheorem name : proposition := proof` checks the proposition and complete
transitive axiom set, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
Derived claims retain named assumptions; conjectures retain proof holes.
Finite tests, native fixtures, environmental propositions, and sketches have
distinct evidence labels. Lean checks the statement as written.

Keep the computational core pure and effects in adapters. Use a `WorldClaim`
as an explicit theorem hypothesis for FFI or other external behavior.
Kernel proofs cover Lean's model; conformance fixtures record runtime evidence.

The [library contracts](LeanEvidence/Contracts/Core.lean) prove axiom
policy, assumption identity, receipt counts, verdicts, and completion rules
over the functions the commands use.
[Report contracts](LeanEvidence/Contracts/Report.lean) prove that JSON
readback preserves evidence fields and receipts. Regression tests cover elaboration,
imports, failed-test rollback, and source metadata.

```sh
lake build
lake test
```

`lake test` builds the libraries and regression suite, then runs the report checks.
To run that Lean script directly after building:

```sh
lake env lean --run Scripts/ReportSmoke.lean
```

Lean checks the file and calls its `main` using Lake's toolchain and import paths.
The script checks imported evidence and source metadata and writes
`/tmp/lean-evidence-example.json`. Reports are generated from compiled modules.
