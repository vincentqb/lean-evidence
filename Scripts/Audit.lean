module

public meta import LeanEvidence.Report

public section
meta section

open Lean LeanEvidence

namespace Scripts.Audit

def run : IO Unit := do
  let imports : Array Import := #[
    { module := `LeanEvidence },
    { module := `LeanEvidence.Report },
    { module := `Examples }
  ]
  let (contracts, examples) ← Report.withEnvironment imports do
    return (← Report.collectEntries `LeanEvidence.Contracts,
      ← Report.collectEntries `Examples.ConstantFolding)
  unless contracts.size == 12 && contracts.all (fun e =>
      e.evidence.kind == .proven && e.evidence.isComplete &&
      !e.evidence.ownHole && e.evidence.assumptions.isEmpty &&
      e.axioms.all standardAxioms.contains && e.source.isSome) do
    throw <| IO.userError "Library contracts lost a kernel-checked contract or its imported metadata"
  unless examples.size == 7 &&
      (examples.filter (·.evidence.kind == .proven)).size == 5 &&
      (examples.filter (·.evidence.kind == .unitTest)).size == 2 do
    throw <| IO.userError "Example must distinguish five universal proofs from two finite tests"
  unless examples.all (fun e =>
      e.axioms.all standardAxioms.contains && e.source.isSome) do
    throw <| IO.userError "Imported example lost its proof audit or source metadata"
  let report := Json.arr ((contracts ++ examples).map Report.entryToJson)
  let path : System.FilePath := "/tmp/lean-evidence-audit.json"
  IO.FS.writeFile path report.pretty
  let reread ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  unless reread == report do
    throw <| IO.userError "Writing and parsing the JSON report changed its evidence"
  IO.println s!"Checked 12 library contract proofs, 5 example proofs, and 2 finite tests; report: {path}"

end Scripts.Audit

def main : IO Unit := Scripts.Audit.run
