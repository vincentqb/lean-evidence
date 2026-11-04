# Working on LeanEvidence

Use the stable Lean version pinned in `lean-toolchain`. This project supports
that version only; remove obsolete compatibility paths when upgrading.

Use `README.md` and the compiled `Examples/ConstantFolding/` example as the
authoring reference: precise statements, independent semantics, and explicit proofs.

Use Lean's `module` system. Export the intended API with `public`; expose
definition bodies with `@[expose]` only when clients need reduction. Elaboration
helpers belong in `meta` sections. Proof modules may use `import all` to inspect
implementation bodies in this package. Keep `autoImplicit` disabled and the
macro dependency graph acyclic.

Keep the computational core pure and effects in adapters. Represent external
behavior as explicit `WorldClaim` hypotheses; keep runtime conformance evidence
distinct from kernel proofs of the Lean model. Avoid incidental comments.

When changing an evidence check, update its regression tests and library contracts.
A test receipt, lint result, or prose assertion is not a proof of
an implementation contract. Never replace missing formalization with `True` or
a `sorry` theorem labelled as proved.

Validate with `lake build` and `lake test`. Tests intentionally exercise
rejected proofs and assumptions, so they are separate from the default libraries.
