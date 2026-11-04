import Lake
open Lake DSL

package «lean_manifests» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanManifests» where
  globs := #[.one `LeanManifests, .submodules `LeanManifests]

@[default_target]
lean_lib «Examples» where
  globs := #[.one `Examples, .submodules `Examples]
