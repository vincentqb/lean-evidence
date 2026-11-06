# Working on LeanEvidence

Use the Lean version pinned in `lean-toolchain`; remove compatibility paths when upgrading.
Use `module`, export the interface with `public`, `@[expose]` only bodies clients must
unfold, keep elaborators in `meta` sections, and keep `autoImplicit` off.

Do not edit `LeanEvidenceManifest.lean`, `comparator.json`, `Audit.lean`,
`Examples/ConstantFolding/Spec.lean`, or `Examples/ConstantFolding/Boundary.lean`; propose
changes instead.

Write claims that cannot be gamed:

- A statement says what its name says; never restate the implementation as its
  specification.
- Mark only suites that exercise their claim with `@[exercises]`.
- Keep effects in the shell and decisions in the core.

When changing a check, add a fixture it rejects to `LeanEvidenceTests/`, and keep
`layering_sound` in `LeanEvidence/Policy.lean` proved. Validate with `lake test`.
