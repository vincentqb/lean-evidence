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
  roots := #[`Examples.ConstantFolding.Claims]
  globs := #[.submodules `Examples]
  precompileModules := true

lean_lib «LeanEvidenceManifest»

@[test_driver]
lean_lib «Tests» where
  roots := #[`Tests]
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]
  needs := #[`@/audit]

@[default_target]
lean_lib «LeanEvidenceAudit»

private def auditPackage (pkg : Package) (entrypoint : System.FilePath) : FetchM (Job Unit) := do
  let mut catalog : Array Name := #[]
  let mut job := Job.nil
  for lib in pkg.leanLibs do
    unless pkg.defaultTargets.contains lib.name do continue
    for mod in ← (← lib.modules.fetch).await do
      if catalog.contains mod.name then continue
      catalog := catalog.push mod.name
      job := job.mix (← mod.leanArts.fetch)
  for exe in pkg.leanExes do
    unless pkg.defaultTargets.contains exe.name do continue
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
