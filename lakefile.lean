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
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

package_facet leanEvidence pkg : Unit := do
  let some audit ← findModule? `LeanEvidence.Audit | error "LeanEvidence.Audit is unavailable"
  let mut catalog : Array Name := #[]
  let mut job := Job.nil.mix (← audit.leanArts.fetch)
  for lib in pkg.leanLibs do
    unless pkg.defaultTargets.contains lib.name do continue
    for mod in ← (← lib.modules.fetch).await do
      unless catalog.contains mod.name do
        catalog := catalog.push mod.name
        job := job.mix (← mod.leanArts.fetch)
  for exe in pkg.leanExes do
    unless pkg.defaultTargets.contains exe.name do continue
    for mod in (← (← exe.root.transImports.fetch).await).push exe.root do
      unless mod.pkg.keyName != pkg.keyName || catalog.contains mod.name do
        catalog := catalog.push mod.name
        job := job.mix (← mod.leanArts.fetch)
  let lean ← getLean
  let env := (← getWorkspace).augmentedEnvVars
  job.mapM fun _ => proc {
    cmd := lean.toString
    args := #["--run", (pkg.dir / "Scripts" / "Audit.lean").toString] ++ catalog.map Name.toString
    cwd := some pkg.dir
    env
  }

@[default_target]
target audit pkg : Unit := do
  return (← pkg.toPackage.fetchFacetJob `leanEvidence).map (fun _ => ())
