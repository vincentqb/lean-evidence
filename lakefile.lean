import Lake
open Lean Lake DSL

package «lean_evidence» where
  builtinLint := true
  fixedToolchain := true
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.redundantVisibility, true⟩,
    ⟨`linter.extra, true⟩
  ]

@[default_target]
lean_lib «LeanEvidence» where
  globs := #[.one `LeanEvidence, .submodules `LeanEvidence]

@[default_target]
lean_lib «Examples» where
  globs := #[.one `Examples, .submodules `Examples]

@[test_driver]
lean_lib «Tests» where
  roots := #[`Tests]
  precompileModules := true
  needs := #[`@/audit]

@[default_target]
lean_lib «LeanEvidenceAudit»

private def auditPackage (pkg : Package) (entrypoint : System.FilePath) : FetchM (Job Unit) := do
  let mut catalog : Array Name := #[]
  let mut job := Job.nil
  for lib in pkg.leanLibs do
    if lib.name.toString == pkg.testDriver then continue
    let modules ← (← lib.modules.fetch).await
    for mod in modules do
      if catalog.contains mod.name then continue
      catalog := catalog.push mod.name
      job := job.mix (← mod.leanArts.fetch)
  for exe in pkg.leanExes do
    if exe.name.toString == pkg.testDriver then continue
    let imports ← (← exe.root.transImports.fetch).await
    for mod in imports.push exe.root do
      if mod.pkg.keyName != pkg.keyName || catalog.contains mod.name then continue
      catalog := catalog.push mod.name
      job := job.mix (← mod.leanArts.fetch)
  let lean ← getLean
  let workspace ← getWorkspace
  job.mapM fun _ => do
    proc {
      cmd := lean.toString
      args := #["--run", (pkg.dir / entrypoint).toString] ++ catalog.map Name.toString
      cwd := some pkg.dir
      env := workspace.augmentedEnvVars
    }

package_facet leanEvidence pkg : Unit :=
  auditPackage pkg "Scripts/Audit.lean"

@[default_target]
target audit pkg : Unit :=
  auditPackage pkg.toPackage "LeanEvidenceAudit.lean"
