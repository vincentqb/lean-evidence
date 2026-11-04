module

meta import Tests.Support
public meta import LeanManifests.Tools
public meta import LeanManifests.Conformance
import Tests.Evidence

public section
meta section

open Lean Elab Command LeanManifests

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
  let items ← liftCoreM <| Workplan.collect `Tests.Evidence
  let rows ← IO.ofExcept items.getArr?
  let some blocked := rows.find? (fun row =>
      match row.getObjValAs? String "name" with
      | .ok name => name == "Tests.Evidence.blocked"
      | .error _ => false)
    | throwError "Missing authored work item"
  let dependencies ← IO.ofExcept <| blocked.getObjValAs? (Array String) "blocked_on"
  unless dependencies == #["Tests.Evidence.future"] do
    throwError "Completed proof must not remain a scheduling dependency"
  unless (← IO.ofExcept <| blocked.getObjValAs? Bool "entry_point") == false do
    throwError "Blocked entry cannot be an entry point"
  unless (← IO.ofExcept <| blocked.getObjValAs? Nat "estimated_minutes") == 15 do
    throwError "Authored work estimate was lost"

run_cmd do
  let parsed ← IO.ofExcept <| LatexRoundtrip.parseMarkers
    "é λ \\manifestThm{Tests.claim}\n% \\manifestThm{ignored}\n\
    \\manifestSym {Tests.symbol}{x_{n}+\\{y\\}} \\manifestThmSuffix{ignored}"
  unless parsed.thmRefs == #["Tests.claim"] &&
      parsed.symRefs == #[("Tests.symbol", "x_{n}+\\{y\\}")] do
    throwError "Unicode, comments, command boundaries, or nested groups broke marker parsing"
  for malformed in ["\\manifestThm{}", "\\manifestThm{open", "\\manifestSym{x}",
      "\\manifestThm x"] do
    match LatexRoundtrip.parseMarkers malformed with
    | .error _ => pure ()
    | .ok _ => throwError "Accepted malformed marker: {malformed}"
  let report := Json.arr #[
    Json.mkObj [("name", Json.str "Tests.claim")],
    Json.mkObj [("name", Json.str "Tests.unreferenced")]
  ]
  let result ← IO.ofExcept <| LatexRoundtrip.check
    "\\manifestThm{Tests.claim}\\manifestThm{Tests.claim}\\manifestThm{Tests.missing}" report
  unless result.resolved == #["Tests.claim"] && result.unresolved == #["Tests.missing"] &&
      result.unreferenced == #["Tests.unreferenced"] do
    throwError "Marker resolution must preserve missing and unreferenced names"
  for malformed in [Json.null, Json.arr #[Json.str "bad"],
      Json.arr #[Json.mkObj [("name", Json.str "")]],
      Json.arr #[Json.mkObj [("name", Json.str "x")], Json.mkObj [("name", Json.str "x")]]] do
    match LatexRoundtrip.check "" malformed with
    | .error _ => pure ()
    | .ok _ => throwError "Accepted a malformed report"

open LeanManifests.Conformance
run_cmd do
  unless approxEq 1.0 1.00001 0.001 &&
      !approxEqArray #[1.0] #[1.0, 2.0] 0.001 &&
      !approxEq 1.0 1.0 0.0 &&
      !approxEq (0.0 / 0.0) 1.0 0.001 &&
      !approxEq (1.0 / 0.0) (1.0 / 0.0) 0.001 &&
      normalizedEq " a\r\nb " "a\nb" &&
      !normalizedEq "a  b" "a b" &&
      rowMultisetEq #["b", "a", "a"] #["a", "b", "a"] &&
      !rowMultisetEq #["a", "a"] #["a"] do
    throwError "Comparison helper changed length, tolerance, whitespace, or multiplicity semantics"

end Tests.Reporting
