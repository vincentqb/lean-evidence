module

public meta import LeanEvidence
public meta import Examples

public section
meta section

open Lean LeanEvidence

namespace LeanEvidenceAudit

def project : Project := {
  modules := #[
    ⟨`LeanEvidence, .core⟩,
    ⟨`LeanEvidence.Evidence, .core⟩,
    ⟨`LeanEvidence.Policy, .core⟩,
    ⟨`LeanEvidence.Commands, .tooling⟩,
    ⟨`LeanEvidence.Contracts, .tooling⟩,
    ⟨`LeanEvidence.Report, .tooling⟩,
    ⟨`LeanEvidence.Audit, .tooling⟩,
    ⟨`Examples, .core⟩,
    ⟨`Examples.ConstantFolding.Defs, .core⟩,
    ⟨`Examples.ConstantFolding.Contracts, .core⟩,
    ⟨`LeanEvidenceAudit, .tooling⟩
  ]
}

def run (catalog : Array Name) : IO Unit := do
  let inventory ← Audit.inspect project catalog
  let (contracts, examples) ← Report.withEnvironment #[{ module := `LeanEvidence.Contracts },
      { module := `LeanEvidence.Report }, { module := `Examples }] do
    return (← Report.collectEntries `LeanEvidence.Contracts,
      ← Report.collectEntries `Examples.ConstantFolding)
  unless !contracts.isEmpty && contracts.all (fun e =>
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
  IO.println s!"Checked {inventory.modules.size} modules, {inventory.declarations.size} declarations, \
    {contracts.size} library proofs, 5 example proofs, and 2 finite tests; report: {path}"

end LeanEvidenceAudit

def main (args : List String) : IO Unit :=
  LeanEvidenceAudit.run (args.toArray.map String.toName)
