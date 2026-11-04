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

lean_lib «Tests» where
  roots := #[`Tests]

@[test_driver]
script test do
  let code ← env "lake" #["build", "LeanManifests", "Examples", "Tests"]
  if code != 0 then return code
  env "lean" #["--run", "Scripts/ReportSmoke.lean"]
