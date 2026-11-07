# Working on Lean Software Challenge

Use the Lean version pinned in `lean-toolchain`; remove compatibility paths when upgrading.
Use `module`, export the interface with `public`, `@[expose]` only bodies clients must
unfold, keep elaborators in `meta` sections, and keep `autoImplicit` off.

Do not edit `ConstantFoldingChallenge.lean`, `comparator.json`, `Audit.lean`,
`Examples/ConstantFolding/Spec.lean`, or `Examples/ConstantFolding/Boundary.lean`; propose
changes instead.

Write a challenge that cannot be gamed:

- A statement says what its name says; never restate the implementation as its
  specification.
- Mark only suites that exercise their claim with `@[exercises]`.
- Keep effects in the shell and decisions in the core.

When changing a check, add a fixture it rejects to `SoftwareChallengeTests/`, and keep
`layering_sound` in `SoftwareChallenge/Policy.lean` proved. Validate with `lake test`.
