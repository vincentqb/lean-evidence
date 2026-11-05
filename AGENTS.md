# Working on LeanEvidence

Use the Lean version pinned in `lean-toolchain`; remove compatibility paths when upgrading.
Use `module`, export the interface with `public`, `@[expose]` only bodies clients must
unfold, keep elaborators in `meta` sections, and keep `autoImplicit` off.

Do not edit `LeanEvidenceManifest.lean`, `comparator.json`, `Scripts/Audit.lean`,
`Examples/ConstantFolding/Spec.lean`, or `Examples/ConstantFolding/Boundary.lean`; propose
changes instead.

Write claims that cannot be gamed:

- The headlines together must fail for every trivial implementation, as `fold_closed_literal`
  fails for `fold := id` and `fold_preserves_meaning` for a constant fold.
- A statement says what its name says. Never state `True`, restate the implementation as
  its specification, or weaken a statement until it passes.
- State world assumptions as `WorldClaim` hypotheses, not plain ones; one that cannot hold
  makes every theorem using it vacuous.
- A premise must be strictly smaller than the headline it supports; a claim that restates
  the headline proves nothing.
- Unproved claims stay `Conjecture`s however many `Test`s, `Check`s, or suites back them;
  mark only suites that exercise their claim with `@[exercises]`.
- Keep effects in the shell and decisions in the core.

When changing a check, update `LeanEvidenceTests/` and keep `layering_sound` in
`LeanEvidence/Policy.lean` proved. Validate with `lake build`, `lake lint`, `lake test`, and
`lake comparator`.
