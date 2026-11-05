module

import all Tests.Fixtures.Spec
import all Tests.Fixtures.Core
import all Tests.Fixtures.Shell
import all Tests.Fixtures.Rejected
meta import LeanEvidence.Audit
public meta import LeanEvidence

public section

namespace Tests.Audit

open Tests.Fixtures

Test Identity identity : identity 5 = 5 := by decide

meta section

open Lean LeanEvidence

private def project : Project := {
  layers := #[(`Tests.Fixtures.Spec, .spec), (`Tests.Fixtures.Boundary, .boundary),
    (`Tests.Fixtures.Core, .core), (`Tests.Fixtures.Shell, .shell), (`Tests.Fixtures.Rejected, .core)]
}

private def valid : Array Name :=
  #[`Tests.Fixtures.Boundary, `Tests.Fixtures.Spec, `Tests.Fixtures.Core, `Tests.Fixtures.Shell]

private def inventory (catalog : Array Name) : CoreM Inventory := do
  let found ← catalog.mapM Audit.collect
  return { modules := found.map (·.1), declarations := found.flatMap (·.2) }

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def expect (errors : Array String) (name reason : String) : CoreM Unit := do
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection of {name}: {reason}\n{errors}"

run_cmd Elab.Command.liftCoreM do
  let accepted ← inventory valid
  unless project.check accepted do
    throwError "Valid fixtures were rejected:\n{Audit.violations project accepted}"
  let rejected ← inventory (valid.push `Tests.Fixtures.Rejected)
  if project.check rejected then throwError "Rejected fixtures passed"
  let errors := Audit.violations project rejected
  for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
      ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "initializer"),
      ("bound", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
      ("traced", "dbg builtin"), ("traceValue", "dbg builtin"), ("Rejected.raw", "axioms"),
      ("Rejected.hole", "sorryAx"), ("Tests.Fixtures.Rejected", "may not import")] do
    expect errors name reason
  let reassign (module : Name) (role : Role) : Project :=
    { layers := project.layers.map fun (name, r) => (name, if name == module then role else r) }
  let asBoundary := reassign `Tests.Fixtures.Core .boundary
  expect (Audit.violations asBoundary (← inventory valid))
    "Tests.Fixtures.identity" "not an @[extern] binding"
  let asShell := reassign `Tests.Fixtures.Boundary .shell
  expect (Audit.violations asShell (← inventory valid)) "nativeSucc" "@[extern]"
  let unlisted : Project := { layers := project.layers.filter (·.1 != `Tests.Fixtures.Shell) }
  if unlisted.check accepted then throwError "An unclassified module passed"
  expect (Audit.violations unlisted accepted) "Tests.Fixtures.Shell" "Unclassified"
  expect (← Audit.challengeImports project `Tests.Fixtures.Challenge) "Tests.Fixtures.Core"
    "may import only spec and boundary"

run_cmd Elab.Command.liftTermElabM do
  let world ← Audit.headline `Tests.Fixtures.successor_grows
  let open_ ← Audit.headline `Tests.Fixtures.uses_open
  let discharged ← Audit.headline `Tests.Fixtures.uses_discharged
  let precondition ← Audit.headline `Tests.Fixtures.bounded
  unless world.premises.map (·.claim) == #[`Tests.Fixtures.SuccAgrees] && proved world.premises do
    throwError "A world premise was misread"
  if proved open_.premises then throwError "An open conjecture was reported proved"
  unless proved discharged.premises && discharged.premises.all (·.discharged) do
    throwError "A proved conjecture was not recognised"
  unless precondition.premises.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let missing ← try discard <| Audit.headline `Tests.Missing; pure false catch _ => pure true
  unless missing do throwError "A missing headline passed"
  let headlines ← #[`Tests.Fixtures.uses_unchecked, `Tests.Fixtures.uses_live,
    `Tests.Fixtures.uses_unnamed].mapM fun name => Audit.headline name
  let errors ← Audit.headlineViolations project #[`Tests.Fixtures.Mode.idle] headlines
    (allEvidence (← getEnv))
  expect errors "Unchecked" "no Test, Check, or live suite"
  expect errors "Mode.idle" "core or shell definition"
  expect errors "uses_unnamed" "not a WorldClaim or Conjecture"
  expect errors "CoreClaim" "declare claims in a spec module"
  if errors.any (contains · "ClockAdvances") then throwError "A live suite did not count: {errors}"

end

end Tests.Audit
