# Working on LeanEvidence

Use the Lean version pinned in `lean-toolchain`; remove compatibility paths when upgrading.
Use `module`, export the interface with `public`, `@[expose]` only bodies clients must
unfold, keep elaborators in `meta` sections, and keep `autoImplicit` off.

Do not edit `LeanEvidenceManifest.lean`, `comparator.json`,
`Examples/ConstantFolding/Spec.lean`, or `Examples/ConstantFolding/Boundary.lean`. They are
the statements the template is held to; propose changes instead.

Write claims that cannot be gamed:

- A headline must fail for a trivial implementation; constant folding states that closed
  expressions become literals so that `fold := id` fails.
- A statement says what its name says. Never state `True`, restate the implementation as
  its specification, or weaken a statement until it passes.
- Assumptions are `WorldClaim` hypotheses, never `axiom`s. A world assumption that cannot
  hold makes every theorem using it vacuous.
- A `Test`, `Check`, or `@[exercises]` suite is evidence for a claim, not a proof. Unproved
  claims stay `Conjecture`s; never use `sorry` or `native_decide` outside `Check`, and never
  mark a suite that does not exercise its claim.
- Keep effects in the shell and decisions in the core; foreign code enters only through
  `@[extern]` declarations in a boundary module.

When changing a check, update `Tests/` and keep `layering_sound` in `LeanEvidence/Policy.lean`
proved.
Validate with `lake build`, `lake test`, and `lake comparator`.
