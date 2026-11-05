module

public meta import LeanEvidence.Commands
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import Std.Data.TreeMap.Raw.Lemmas

public section
meta section

open Lean

namespace LeanEvidence.Report

structure Source where
  moduleName : Name
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr

structure Entry where
  name : Name
  evidence : Evidence
  axioms : Array Name
  tests : Option TestResults
  typePP : String
  statement : Option String
  docString : String
  source : Option Source
  deriving Repr

structure Claim where
  fact : ClaimFact
  statement : String
  source : Option Source
  deriving Repr

structure Snapshot where
  inventories : Array Name
  evidence : Array Entry
  claims : Array Claim
  deriving Repr

def Snapshot.facts (snapshot : Snapshot) : Array ClaimFact :=
  snapshot.claims.map (·.fact)

def Snapshot.isComplete (snapshot : Snapshot) : Bool :=
  Claims.isComplete snapshot.inventories snapshot.facts

def Snapshot.theoremIndex (snapshot : Snapshot) : Array Name :=
  snapshot.claims.filterMap fun claim =>
    if claim.fact.kind == .proof && claim.fact.isComplete then claim.fact.evidence else none

def entryNames (env : Environment) (scope : Name) : Array Name :=
  ((evidenceExt.getState env).toArray.map Prod.fst).filter (scope.isPrefixOf ·)
    |>.qsort (fun a b => a.toString < b.toString)

private def sourceLocation (n : Name) : CoreM (Option Source) := do
  let env ← getEnv
  let some ranges ← findDeclarationRangesCore? n | return none
  let some idx := env.getModuleIdxFor? n | return none
  let moduleName := env.allImportedModuleNames[idx.toNat]!
  let r := ranges.range
  return some {
    moduleName
    file := moduleName.toString.replace "." "/" ++ ".lean"
    startLine := r.pos.line
    startColumn := r.pos.column
    endLine := r.endPos.line
    endColumn := r.endPos.column
  }

def buildEntry (n : Name) : CoreM Entry := do
  let env ← getEnv
  let some evidence := getEvidence? env n
    | throwError "{n} has no registered evidence"
  let info ← getConstInfo n
  if evidence.kind.requiresProof then requireProof n
  if evidence.kind == .tested || evidence.kind == .failing then
    Meta.MetaM.run' <| validateTests n
  let axioms := (← collectAxioms n).qsort (fun a b => a.toString < b.toString)
  let typePP := (← Meta.MetaM.run' <| PrettyPrinter.ppExpr info.type).pretty
  let proposition := if evidence.kind == .world then info.value?
    else if evidence.kind == .sketch then none else some info.type
  let statement ← proposition.mapM fun e =>
    return (← Meta.MetaM.run' <| PrettyPrinter.ppExpr e).pretty
  return {
    name := n
    evidence
    axioms
    tests := getTestResults env n
    typePP
    statement
    docString := (← findDocString? env n).getD ""
    source := ← sourceLocation n
  }

def collectEntries (scope : Name) : CoreM (Array Entry) := do
  (entryNames (← getEnv) scope).mapM buildEntry

def collectClaims (inventories : Array Name) : CoreM (Array Claim) := do
  modifyEnv (·.setExporting false)
  let mut result := #[]
  for name in inventories do
    let facts ← Meta.MetaM.run' <| validateRequirements name
    let some claims := getRequirements? (← getEnv) name
      | throwError "{name}: required inventory is unavailable"
    for (claim, fact) in claims.zip facts do
      let proposition ← Meta.MetaM.run' <| requiredStatement claim
      let statement := (← Meta.MetaM.run' <| PrettyPrinter.ppExpr proposition).pretty
      result := result.push { fact, statement, source := ← sourceLocation claim.name }
  return result

def collect (inventories : Array Name) : CoreM Snapshot := do
  let claims ← collectClaims inventories
  let names := claims.filterMap (·.fact.evidence) |>.foldl (fun names name =>
    if names.contains name then names else names.push name) #[]
  return { inventories, claims, evidence := ← names.mapM buildEntry }

private def namesToJson (names : Array Name) : Json :=
  Json.arr (names.map (Json.str ∘ Name.toString))

private def sourceToJson (s : Source) : Json :=
  Json.mkObj [
    ("module", Json.str s.moduleName.toString),
    ("file", Json.str s.file),
    ("start", Json.arr #[toJson s.startLine, toJson s.startColumn]),
    ("end", Json.arr #[toJson s.endLine, toJson s.endColumn])
  ]

def entryToJson (e : Entry) : Json :=
  Json.mkObj [
    ("name", Json.str e.name.toString),
    ("evidence", Json.str (toString e.evidence.kind)),
    ("assumptions", namesToJson e.evidence.assumptions),
    ("own_hole", toJson e.evidence.ownHole),
    ("axioms", namesToJson e.axioms),
    ("tests", e.tests.map (fun t => Json.mkObj [
      ("passed", toJson t.passed),
      ("total", toJson t.total)
    ]) |>.getD Json.null),
    ("type", Json.str e.typePP),
    ("statement", e.statement.map Json.str |>.getD Json.null),
    ("doc", Json.str e.docString),
    ("source", e.source.map sourceToJson |>.getD Json.null)
  ]

def claimToJson (claim : Claim) : Json :=
  Json.mkObj [
    ("inventory", Json.str claim.fact.inventory.toString),
    ("name", Json.str claim.fact.name.toString),
    ("kind", Json.str (if claim.fact.kind == .proof then "proof" else "test")),
    ("statement", Json.str claim.statement),
    ("evidence", claim.fact.evidence.map (Json.str ∘ Name.toString) |>.getD Json.null),
    ("complete", toJson claim.fact.isComplete),
    ("source", claim.source.map sourceToJson |>.getD Json.null)
  ]

def Snapshot.toJson (snapshot : Snapshot) : Json :=
  Json.mkObj [
    ("inventories", namesToJson snapshot.inventories),
    ("claims", Json.arr (snapshot.claims.map claimToJson)),
    ("evidence", Json.arr (snapshot.evidence.map entryToJson)),
    ("theorem_index", namesToJson snapshot.theoremIndex),
    ("outstanding", namesToJson (Claims.outstanding snapshot.facts)),
    ("complete", Lean.toJson snapshot.isComplete)
  ]

def withEnvironment {α : Type} (imports : Array Import) (action : CoreM α) : IO α := do
  if imports.isEmpty then throw <| IO.userError "Supply at least one compiled module to report on"
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let imports := imports.map ({ · with importAll := true })
  let env ← withImporting do
    let (_, state) ← (importModulesCore imports).run
    finalizeImport state imports {} (leakEnv := false) (loadExts := true) (isModule := true)
  let (result, _) ← action.toIO
    { fileName := "<evidence-report>", fileMap := default } { env }
  return result

def run (inventories : Array Name) (outPath : System.FilePath) (imports : Array Import) :
    IO Unit := do
  let snapshot ← withEnvironment imports (collect inventories)
  IO.FS.writeFile outPath snapshot.toJson.pretty
  IO.println s!"Wrote {snapshot.claims.size} required claims to {outPath}; \
    complete: {snapshot.isComplete}"

end LeanEvidence.Report

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

ProvenTheorem report_completion : ∀ snapshot : Report.Snapshot,
    snapshot.toJson.getObjVal? "complete" =
      .ok (toJson (Claims.isComplete snapshot.inventories snapshot.facts)) ∧
    snapshot.toJson.getObjVal? "outstanding" =
      .ok (.arr ((Claims.outstanding snapshot.facts).map (Json.str ∘ Name.toString))) ∧
    snapshot.toJson.getObjVal? "theorem_index" =
      .ok (.arr (snapshot.theoremIndex.map (Json.str ∘ Name.toString))) := by
  intro snapshot
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold Report.Snapshot.toJson
    apply object_field
    · simp [List.pairwise_cons]
    · simp [Report.namesToJson, Report.Snapshot.isComplete]

ProvenTheorem report_claims : ∀ claim : Report.Claim,
    (Report.claimToJson claim).getObjVal? "statement" = .ok (.str claim.statement) ∧
    (Report.claimToJson claim).getObjVal? "evidence" =
      .ok (claim.fact.evidence.map (Json.str ∘ Name.toString) |>.getD .null) ∧
    (Report.claimToJson claim).getObjVal? "complete" = .ok (toJson claim.fact.isComplete) := by
  intro claim
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold Report.claimToJson
    apply object_field
    · simp [List.pairwise_cons]
    · simp

ProvenTheorem theorem_index_iff : ∀ (snapshot : Report.Snapshot) name,
    name ∈ snapshot.theoremIndex ↔ ∃ claim ∈ snapshot.claims,
      claim.fact.kind = .proof ∧ claim.fact.isComplete = true ∧
        claim.fact.evidence = some name := by
  intro snapshot name
  simp [Report.Snapshot.theoremIndex, Array.mem_filterMap]
  grind

Requirements reportObligations where
  proof evidence : ∀ e : Report.Entry,
    (Report.entryToJson e).getObjVal? "evidence" = .ok (.str (toString e.evidence.kind)) ∧
    (Report.entryToJson e).getObjVal? "assumptions" =
      .ok (.arr (e.evidence.assumptions.map (Json.str ∘ Name.toString))) ∧
    (Report.entryToJson e).getObjVal? "own_hole" = .ok (toJson e.evidence.ownHole) ∧
    (Report.entryToJson e).getObjVal? "axioms" =
      .ok (.arr (e.axioms.map (Json.str ∘ Name.toString))) := report_evidence
  proof tests : ∀ (e : Report.Entry) (r : TestResults), e.tests = some r →
    ((Report.entryToJson e).getObjVal? "tests").bind (·.getObjVal? "passed") =
      .ok (toJson r.passed) ∧
    ((Report.entryToJson e).getObjVal? "tests").bind (·.getObjVal? "total") =
      .ok (toJson r.total) := report_tests
  proof no_tests : ∀ e : Report.Entry,
    e.tests = none → (Report.entryToJson e).getObjVal? "tests" = .ok .null := report_no_tests
  proof completion : ∀ snapshot : Report.Snapshot,
    snapshot.toJson.getObjVal? "complete" =
      .ok (toJson (Claims.isComplete snapshot.inventories snapshot.facts)) ∧
    snapshot.toJson.getObjVal? "outstanding" =
      .ok (.arr ((Claims.outstanding snapshot.facts).map (Json.str ∘ Name.toString))) ∧
    snapshot.toJson.getObjVal? "theorem_index" =
      .ok (.arr (snapshot.theoremIndex.map (Json.str ∘ Name.toString))) := report_completion
  proof claims : ∀ claim : Report.Claim,
    (Report.claimToJson claim).getObjVal? "statement" = .ok (.str claim.statement) ∧
    (Report.claimToJson claim).getObjVal? "evidence" =
      .ok (claim.fact.evidence.map (Json.str ∘ Name.toString) |>.getD .null) ∧
    (Report.claimToJson claim).getObjVal? "complete" = .ok (toJson claim.fact.isComplete) :=
    report_claims
  proof theorem_index : ∀ (snapshot : Report.Snapshot) name,
    name ∈ snapshot.theoremIndex ↔ ∃ claim ∈ snapshot.claims,
      claim.fact.kind = .proof ∧ claim.fact.isComplete = true ∧
        claim.fact.evidence = some name := theorem_index_iff

end LeanEvidence.Contracts
