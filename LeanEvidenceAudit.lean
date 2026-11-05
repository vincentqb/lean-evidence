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
  requirements := #[`LeanEvidence.Contracts.obligations, `LeanEvidence.Contracts.reportObligations,
    `Examples.ConstantFolding.obligations]
}

def run (catalog : Array Name) : IO Unit := do
  let inventory ← Audit.inspect project catalog
  let (snapshot, available) ← Report.withEnvironment #[{ module := `LeanEvidence.Contracts },
      { module := `LeanEvidence.Report }, { module := `Examples }] do
    let snapshot ← Report.collect project.requirements
    let env ← getEnv
    return (snapshot, Report.entryNames env `LeanEvidence.Contracts ++
      Report.entryNames env `Examples.ConstantFolding)
  unless snapshot.isComplete && (Claims.outstanding snapshot.facts).isEmpty do
    throw <| IO.userError "Required evidence is incomplete"
  unless snapshot.claims.size == inventory.claims.size && snapshot.facts.all (fun claim =>
      inventory.claims.any (fun checked =>
        claim.name == checked.name && claim.inventory == checked.inventory &&
          claim.kind == checked.kind && claim.evidence == checked.evidence &&
          claim.verified == checked.verified)) do
    throw <| IO.userError "Architecture audit and evidence report disagree on required claims"
  unless available.all (fun name => snapshot.evidence.any (·.name == name)) do
    throw <| IO.userError "A library or example contract is missing from its Requirements inventory"
  unless snapshot.evidence.all (fun e =>
      e.evidence.isComplete && !e.evidence.ownHole && e.evidence.assumptions.isEmpty &&
      e.axioms.all standardAxioms.contains && e.source.isSome) do
    throw <| IO.userError "Required evidence lost its kernel proof or source metadata"
  unless snapshot.claims.all (·.source.isSome) do
    throw <| IO.userError "A required claim lost its source metadata"
  let report := snapshot.toJson
  let path : System.FilePath := "/tmp/lean-evidence-audit.json"
  IO.FS.writeFile path report.pretty
  let reread ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  unless reread == report do
    throw <| IO.userError "Writing and parsing the JSON report changed its evidence"
  IO.println s!"Checked {inventory.modules.size} modules, {inventory.declarations.size} declarations, \
    and {snapshot.claims.size} required claims \
    ({snapshot.theoremIndex.size} proofs, \
    {(snapshot.facts.filter (·.kind == .test)).size} tests); report: {path}"

end LeanEvidenceAudit

def main (args : List String) : IO Unit :=
  LeanEvidenceAudit.run (args.toArray.map String.toName)
