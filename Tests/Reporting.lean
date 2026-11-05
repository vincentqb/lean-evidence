module

meta import Tests.Support
public meta import LeanEvidence.Report
import all Tests.Evidence

public section
meta section

open Lean Elab Command LeanEvidence

namespace Tests.Reporting

/-- A report must match namespace components, including local entries. -/
Sketch scope

end Tests.Reporting

namespace Tests.ReportingExtra
/-- This must not leak into a report for Tests.Reporting. -/
Sketch excluded
end Tests.ReportingExtra

namespace Tests.Reporting

run_cmd do
  let env ← getEnv
  unless Report.entryNames env `Tests.Reporting == #[`Tests.Reporting.scope] do
    throwError "Report scope includes a neighbouring namespace or misses local evidence"
  let entry ← liftCoreM <| Report.buildEntry `Tests.Evidence.passing_samples
  unless entry.evidence.kind == .tested && entry.axioms.contains ``sorryAx do
    throwError "Imported conjecture evidence or axioms were lost"
  let some receipts := entry.tests | throwError "Imported test receipts were lost"
  unless receipts.passed == 2 && receipts.total == 2 do
    throwError "Imported test receipts were lost"
  let world ← liftCoreM <| Report.buildEntry `Tests.Evidence.intact
  unless world.evidence.kind == .world && world.statement.isSome && world.axioms.isEmpty do
    throwError "A WorldClaim must report its proposition without assuming it"
  let json := Report.entryToJson entry
  unless (← IO.ofExcept <| json.getObjValAs? String "evidence") == "TestedConjecture" do
    throwError "JSON changed the evidence label"

run_cmd Lean.Elab.Command.liftCoreM do
  let ready ← Report.collect #[`Tests.Evidence.ready]
  unless ready.isComplete && ready.claims.size == 3 && ready.evidence.size == 3 &&
      ready.theoremIndex == #[`Tests.Evidence.headline, `Tests.Evidence.clean] &&
      (Claims.outstanding ready.facts).isEmpty do
    throwError "Compiled witnesses did not complete their required claims"
  unless ready.claims.all (fun claim => !claim.statement.isEmpty) do
    throwError "A required proposition was lost from the report"
  let root ← Report.collect #[`Tests.Evidence.root_inventory]
  unless root.isComplete && root.claims[0]?.map (·.fact.name) ==
      some `Tests.Evidence.root_inventory.identity do
    throwError "A root-qualified inventory was not collected"
  let pending ← Report.collect #[`Tests.Evidence.pending]
  unless !pending.isComplete && pending.theoremIndex == #[`Tests.Evidence.headline] &&
      Claims.outstanding pending.facts ==
        #[`Tests.Evidence.pending.commutativity, `Tests.Evidence.pending.addition] do
    throwError "Outstanding proof and test requirements were lost"
  let json ← IO.ofExcept <| Json.parse pending.toJson.compress
  unless !(← IO.ofExcept <| json.getObjValAs? Bool "complete") &&
      (← IO.ofExcept <| json.getObjValAs? (Array String) "outstanding") ==
        #["Tests.Evidence.pending.commutativity", "Tests.Evidence.pending.addition"] &&
      (← IO.ofExcept <| json.getObjValAs? (Array String) "theorem_index") ==
        #["Tests.Evidence.headline"] do
    throwError "JSON completion, theorem index, and outstanding claims disagree"

rejects "disagrees with its registered claims" in
  run_cmd do
    let some claims := getRequirements? (← getEnv) `Tests.Evidence.ready
      | throwError "Missing inventory"
    modifyEnv fun env => requirementsExt.addEntry env (`Tests.Evidence.ready, claims.pop)
    liftTermElabM <| discard <| validateRequirements `Tests.Evidence.ready

rejects "wrong evidence kind" in
  run_cmd do
    let some claims := getRequirements? (← getEnv) `Tests.Evidence.ready
      | throwError "Missing inventory"
    liftTermElabM <| discard <| validateRequirement `Tests.Evidence.ready
      { claims[0]! with kind := .test }

rejects "does not prove the required proposition" in
  run_cmd do
    let some claims := getRequirements? (← getEnv) `Tests.Evidence.ready
      | throwError "Missing inventory"
    liftTermElabM <| discard <| validateRequirement `Tests.Evidence.ready
      { claims[0]! with evidence := some `Tests.Evidence.explicit_hypothesis }

rejects "disagrees with its registered evidence" in
  run_cmd do
    let some claims := getRequirements? (← getEnv) `Tests.Evidence.ready
      | throwError "Missing inventory"
    liftTermElabM <| discard <| validateRequirement `Tests.Evidence.ready
      { claims[0]! with evidence := none }

rejects "receipt disagrees with its proof" in
  run_cmd do
    modifyEnv fun env => testCasesExt.addEntry env (`Tests.Evidence.passing_samples, {
      statement := `Tests.Evidence.passing_samples_case_1
      receipt := `Tests.Evidence.samples_result_2
      witness := some `Tests.Evidence.passing_samples_test_1
    })
    liftCoreM <| discard <| Report.buildEntry `Tests.Evidence.passing_samples

rejects "test proof has the wrong proposition" in
  run_cmd do
    modifyEnv fun env => testCasesExt.addEntry env (`Tests.Evidence.passing_samples, {
      statement := `Tests.Evidence.passing_samples_case_1
      receipt := `Tests.Evidence.passing_samples_result_1
      witness := some `Tests.Evidence.headline
    })
    liftCoreM <| discard <| Report.buildEntry `Tests.Evidence.passing_samples

end Tests.Reporting
