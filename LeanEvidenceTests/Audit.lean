module

import all LeanEvidenceTests.Fixtures.Spec
import all LeanEvidenceTests.Fixtures.Core
import all LeanEvidenceTests.Fixtures.Shell
import all LeanEvidenceTests.Fixtures.Rejected
meta import LeanEvidence.Audit
public meta import LeanEvidence

public section

namespace LeanEvidenceTests.Audit

open LeanEvidenceTests.Fixtures

Test Identity identity : identity 5 = 5 := by decide

meta section

open Lean LeanEvidence

private def project : Project := {
  layers := #[(`LeanEvidenceTests.Fixtures.Spec, .spec),
    (`LeanEvidenceTests.Fixtures.Boundary, .boundary), (`LeanEvidenceTests.Fixtures.Core, .core),
    (`LeanEvidenceTests.Fixtures.Shell, .shell), (`LeanEvidenceTests.Fixtures.Rejected, .core)]
}

private def valid : Array Name := #[`LeanEvidenceTests.Fixtures.Boundary,
  `LeanEvidenceTests.Fixtures.Spec, `LeanEvidenceTests.Fixtures.Core,
  `LeanEvidenceTests.Fixtures.Shell]

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def expect (errors : Array String) (name reason : String) : CoreM Unit := do
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection of {name}: {reason}\n{errors}"

#guard ({ layers := #[(`A, .tooling), (`A.B.C, .core), (`A.B, .spec)] } : Project).role?
  `A.B.C.D == some .core

run_cmd Elab.Command.liftCoreM do
  let accepted ← Audit.collect valid
  unless project.check accepted do
    throwError "Valid fixtures were rejected:\n{Audit.violations project accepted}"
  let reassign (module : Name) (role : Role) : Project :=
    { layers := project.layers.map fun (name, r) => (name, if name == module then role else r) }
  let rejected ← Audit.collect (valid.push `LeanEvidenceTests.Fixtures.Rejected)
  for layout in #[project, reassign `LeanEvidenceTests.Fixtures.Rejected .spec] do
    if layout.check rejected then throwError "Rejected fixtures passed"
    for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
        ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "initializer"),
        ("bound", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
        ("traced", "dbg builtin"), ("traceValue", "dbg builtin"), ("Rejected.raw", "axioms"),
        ("chained", "Rejected.raw"), ("Rejected.hole", "sorryAx"),
        ("Fixtures.Rejected", "may not import")] do
      expect (Audit.violations layout rejected) name reason
  for (module, role, facts, name, reason) in #[
      (`LeanEvidenceTests.Fixtures.Core, Role.boundary, accepted, "identity",
        "not an @[extern] binding"),
      (`LeanEvidenceTests.Fixtures.Boundary, .core, accepted, "Fixtures.Spec", "may not import"),
      (`LeanEvidenceTests.Fixtures.Shell, .boundary, accepted, "Fixtures.Shell", "may not import"),
      (`LeanEvidenceTests.Fixtures.Core, .tooling, accepted, "Fixtures.Shell", "may not import"),
      (`LeanEvidenceTests.Fixtures.Rejected, .shell, rejected, "hiddenUnsafe", "unsafe"),
      (`LeanEvidenceTests.Fixtures.Rejected, .shell, rejected, "bound", "@[extern]"),
      (`LeanEvidenceTests.Fixtures.Rejected, .shell, rejected, "Rejected.replaced",
        "@[implemented_by]"),
      (`LeanEvidenceTests.Fixtures.Rejected, .tooling, rejected, "Rejected.raw", "axioms")] do
    expect (Audit.violations (reassign module role) facts) name reason
  let legacy := { accepted with
    modules := accepted.modules.map ({ · with usesModuleSystem := false }) }
  if project.check legacy then throwError "A file without `module` passed"
  expect (Audit.violations project legacy) "Fixtures.Core" "start the file with `module`"
  let unlisted : Project :=
    { layers := project.layers.filter (·.1 != `LeanEvidenceTests.Fixtures.Shell) }
  if unlisted.check accepted then throwError "An unclassified module passed"
  expect (Audit.violations unlisted accepted) "Fixtures.Shell" "Unclassified"
  let challenge ← Audit.challengeImports project `LeanEvidenceTests.Fixtures.Challenge
  expect challenge "Fixtures.Core" "may import only spec and boundary"
  expect challenge "imports LeanEvidence;" "may import only spec and boundary"

run_cmd Elab.Command.liftTermElabM do
  let world ← Audit.headline `LeanEvidenceTests.Fixtures.successor_grows
  let open_ ← Audit.headline `LeanEvidenceTests.Fixtures.uses_open
  let discharged ← Audit.headline `LeanEvidenceTests.Fixtures.uses_discharged
  let precondition ← Audit.headline `LeanEvidenceTests.Fixtures.bounded
  unless world.premises.map (·.claim) == #[`LeanEvidenceTests.Fixtures.SuccAgrees] &&
      proved world.premises do
    throwError "A world premise was misread"
  if proved open_.premises then throwError "An open conjecture was reported proved"
  unless proved discharged.premises && discharged.premises.all (·.discharged) do
    throwError "A proved conjecture was not recognised"
  unless precondition.premises.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let missing ← try discard <| Audit.headline `LeanEvidenceTests.Missing; pure false catch _ => pure true
  unless missing do throwError "A missing headline passed"
  let headlines ← #[`LeanEvidenceTests.Fixtures.uses_unchecked,
    `LeanEvidenceTests.Fixtures.uses_live, `LeanEvidenceTests.Fixtures.uses_unnamed].mapM
    fun name => Audit.headline name
  let errors ← Audit.headlineViolations project #[`LeanEvidenceTests.Fixtures.EvenFour]
    (headlines.push world) (allEvidence (← getEnv))
  expect errors "Unchecked" "no Test, Check, or live suite"
  expect errors "EvenFour" "core or shell definition"
  expect errors "uses_unnamed" "not a WorldClaim or Conjecture"
  expect errors "CoreClaim" "declare claims in a spec module"
  if errors.any (fun e => contains e "ClockAdvances" || contains e "SuccAgrees") then
    throwError "Evidence did not count: {errors}"

end

end LeanEvidenceTests.Audit
