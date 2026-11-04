module

meta import Tests.Support
public meta import LeanEvidence.Report
import Tests.Evidence

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
end Tests.Reporting
