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
  globs := #[.andSubmodules `LeanEvidence]

@[default_target]
lean_lib «Examples» where
  roots := #[`Examples.ConstantFolding.Claims]
  globs := #[.submodules `Examples.ConstantFolding]
  precompileModules := true

lean_lib «LeanEvidenceManifest»

@[test_driver]
lean_lib «LeanEvidenceTests» where
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

package_facet leanEvidence pkg : Unit := do
  let some audit ← findModule? `LeanEvidence.Audit | error "LeanEvidence.Audit is unavailable"
  let mut catalog : Array Name := #[]
  let mut job := Job.nil.mix (← audit.leanArts.fetch)
  for root in ← (← pkg.defaultModules.fetch).await do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || catalog.contains mod.name do
        catalog := catalog.push mod.name
        job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do proc {
    cmd := (← getLean).toString
    args := #["--run", (pkg.dir / "Audit.lean").toString] ++ catalog.map Name.toString
    cwd := some pkg.dir
    env := ← getAugmentedEnv
  }

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `leanEvidence).map (fun _ => ())
