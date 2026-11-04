module

public meta import LeanEvidence.Report
import all LeanEvidence.Report
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import Std.Data.TreeMap.Raw.Lemmas

public section
meta section

open Lean

namespace LeanEvidence.Contracts

private theorem object_field (fields : List (String × Json)) (key : String) (value : Json)
    (distinct : fields.Pairwise (fun a b => compare a.1 b.1 ≠ .eq))
    (present : (key, value) ∈ fields) :
    (Json.mkObj fields).getObjVal? key = .ok value := by
  unfold Json.mkObj Json.getObjVal?
  dsimp only
  rw [Std.TreeMap.Raw.get?_eq_getElem?]
  rw [Std.TreeMap.Raw.getElem?_ofList_of_mem
    (k := key) (v := value) (by simp) distinct present]
  rfl

ProvenTheorem report_evidence : ∀ e : Report.Entry,
    (Report.entryToJson e).getObjVal? "evidence" = .ok (.str (toString e.evidence.kind)) ∧
    (Report.entryToJson e).getObjVal? "assumptions" =
      .ok (.arr (e.evidence.assumptions.map (Json.str ∘ Name.toString))) ∧
    (Report.entryToJson e).getObjVal? "own_hole" = .ok (toJson e.evidence.ownHole) ∧
    (Report.entryToJson e).getObjVal? "axioms" =
      .ok (.arr (e.axioms.map (Json.str ∘ Name.toString))) := by
  intro e
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold Report.entryToJson
    apply object_field
    · simp [List.pairwise_cons]
    · simp [Report.namesToJson]

ProvenTheorem report_tests : ∀ (e : Report.Entry) (r : TestResults),
    e.tests = some r →
    ((Report.entryToJson e).getObjVal? "tests").bind (·.getObjVal? "passed") =
      .ok (toJson r.passed) ∧
    ((Report.entryToJson e).getObjVal? "tests").bind (·.getObjVal? "total") =
      .ok (toJson r.total) := by
  intro e r tests
  have encoded : (Report.entryToJson e).getObjVal? "tests" =
      .ok (Json.mkObj [("passed", toJson r.passed), ("total", toJson r.total)]) := by
    unfold Report.entryToJson
    apply object_field
    · simp [List.pairwise_cons]
    · simp [tests]
  constructor
  all_goals
    rw [encoded]
    change (Json.mkObj _).getObjVal? _ = _
    apply object_field
    · simp [List.pairwise_cons]
    · simp

ProvenTheorem report_no_tests : ∀ e : Report.Entry,
    e.tests = none → (Report.entryToJson e).getObjVal? "tests" = .ok .null := by
  intro e tests
  unfold Report.entryToJson
  apply object_field
  · simp [List.pairwise_cons]
  · simp [tests]

attribute [theorems report_evidence report_tests report_no_tests] Report.entryToJson

end LeanEvidence.Contracts
