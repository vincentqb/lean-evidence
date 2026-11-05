module

public import Tests.Fixtures.Rejected
import all Tests.Fixtures.Spec
import all Tests.Fixtures.Core
import all Tests.Fixtures.Shell
import all Tests.Fixtures.Rejected
meta import LeanEvidence.Audit

public section
meta section

open Lean LeanEvidence

namespace Tests.Audit

private def project : Project := {
  layers := #[
    (`Tests.Fixtures.Spec, .spec),
    (`Tests.Fixtures.Boundary, .boundary),
    (`Tests.Fixtures.Core, .core),
    (`Tests.Fixtures.Shell, .shell),
    (`Tests.Fixtures.Rejected, .core)
  ]
  trusted := #[`Init, `Std, `Lean, `LeanEvidence]
}

private def valid : Array Name :=
  #[`Tests.Fixtures.Boundary, `Tests.Fixtures.Spec, `Tests.Fixtures.Core, `Tests.Fixtures.Shell]

private def expect (errors : Array String) (name reason : String) : CoreM Unit := do
  let contains (text fragment : String) := (text.splitOn fragment).length > 1
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection of {name}: {reason}\n{errors}"

run_cmd Elab.Command.liftCoreM do
  let accepted ← Audit.collect project valid
  unless project.check valid accepted do
    throwError "Valid fixtures were rejected:\n{Audit.violations project valid accepted}"
  let all := valid.push `Tests.Fixtures.Rejected
  let rejected ← Audit.collect project all
  if project.check all rejected then throwError "Rejected fixtures passed"
  let errors := Audit.violations project all rejected
  for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
      ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "initializer"),
      ("bound", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
      ("traced", "dbgTrace"), ("throughShell", "IO"), ("Rejected.raw", "axioms"),
      ("Rejected.hole", "sorryAx"), ("Tests.Fixtures.Rejected", "may not import")] do
    expect errors name reason
  let reassign (module : Name) (role : Role) : Project :=
    { project with layers := project.layers.map fun (name, r) => (name, if name == module then role else r) }
  let asBoundary := reassign `Tests.Fixtures.Core .boundary
  expect (Audit.violations asBoundary valid (← Audit.collect asBoundary valid))
    "Tests.Fixtures.identity" "not an @[extern] binding"
  let asShell := reassign `Tests.Fixtures.Boundary .shell
  expect (Audit.violations asShell valid (← Audit.collect asShell valid))
    "nativeSucc" "@[extern]"
  let unlisted := { project with layers := project.layers.filter (·.1 != `Tests.Fixtures.Shell) }
  unless !unlisted.check valid accepted do throwError "An unclassified module passed"
  expect (Audit.violations unlisted valid accepted) "Tests.Fixtures.Shell" "Unclassified"
  let duplicated := { project with layers := project.layers.push (`Tests.Fixtures.Core, .core) }
  unless !duplicated.check valid accepted do throwError "A duplicated layer passed"
  unless !project.check (valid.push `Tests.Missing) accepted do
    throwError "A module missing from the inventory passed"

run_cmd Elab.Command.liftTermElabM do
  let world ← Audit.headline `Tests.Fixtures.uses_world
  let open_ ← Audit.headline `Tests.Fixtures.uses_open
  let discharged ← Audit.headline `Tests.Fixtures.uses_discharged
  let plain ← Audit.headline `Tests.Fixtures.successor_grows
  unless world.premises.map (·.claim) == #[`Tests.Fixtures.SuccAgrees] &&
      level world.premises == .proved do
    throwError "A world premise was misread: {repr world}"
  unless level open_.premises == .derived && open_.premises.all (!·.discharged) do
    throwError "An open conjecture was reported proved: {repr open_}"
  unless level discharged.premises == .proved && discharged.premises.all (·.discharged) do
    throwError "A proved conjecture was not recognised: {repr discharged}"
  unless plain.premises.size == 1 do throwError "Data binders were read as premises"
  let config : Audit.Config := {
    challenge := `LeanEvidenceManifest
    solution := `LeanEvidenceClaims
    theorems := #[`Tests.Fixtures.uses_unchecked]
    holes := #[`Tests.Fixtures.Mode.idle]
  }
  let errors ← Audit.headlineViolations project config
    #[← Audit.headline `Tests.Fixtures.uses_unchecked]
  expect errors "Unchecked" "no Test or Check"
  expect errors "Mode.idle" "core or shell definition"

end Tests.Audit
