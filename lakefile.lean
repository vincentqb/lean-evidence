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
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (pkg.dir / "comparator.json"))
  let challenge ← IO.ofExcept <| config.getObjValAs? String "challenge_module"
  let mut catalog : Array Name := #[]
  let mut job := Job.nil.mix (← audit.leanArts.fetch)
  for root in ← (← pkg.defaultModules.fetch).await do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || catalog.contains mod.name do
        catalog := catalog.push mod.name
        job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    for file in [pkg.dir / "Audit.lean", pkg.dir / "comparator.json",
        modToFilePath pkg.dir challenge.toName "lean"] do
      addTrace (← BuildTrace.compute (TextFilePath.mk file))
    -- Rerun only when an input changes, and print the report only when rerun.
    let report := pkg.buildDir / "leanEvidence.txt"
    let upToDate ← buildUnlessUpToDate? report (← getTrace) (report.addExtension "trace") do
      IO.FS.writeFile report (← captureProc {
        cmd := (← getLean).toString
        args := #["--run", (pkg.dir / "Audit.lean").toString] ++ catalog.map Name.toString
        cwd := some pkg.dir
        env := ← getAugmentedEnv
      })
    unless upToDate do logInfo (← IO.FS.readFile report)

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `leanEvidence).map (fun _ => ())
