module

public meta import LeanManifests.Tools

public section
meta section

open Lean LeanManifests

namespace Scripts.ReportSmoke

def run : IO Unit := do
  let imports : Array Import := #[
    { module := `LeanManifests },
    { module := `LeanManifests.Tools },
    { module := `Examples }
  ]
  let (contracts, examples, index, workplan) ← Report.withEnvironment imports do
    return (← Report.collectEntries `LeanManifests.Contracts,
      ← Report.collectEntries `Examples.ConstantFolding,
      ← IndexGen.buildIndex `Examples.ConstantFolding,
      ← Workplan.collect `LeanManifests.Contracts)
  unless contracts.size == 13 && contracts.all (fun e =>
      e.evidence.kind == .proven && !e.evidence.ownHole && e.evidence.assumptions.isEmpty &&
      e.axioms.all standardAxioms.contains && e.source.isSome) do
    throw <| IO.userError "Self-manifest lost a kernel-checked contract or its imported metadata"
  unless examples.size == 7 &&
      (examples.filter (·.evidence.kind == .proven)).size == 5 &&
      (examples.filter (·.evidence.kind == .unitTest)).size == 2 do
    throw <| IO.userError "Example must distinguish five universal proofs from two finite tests"
  unless examples.all (fun e =>
      e.axioms.all standardAxioms.contains && e.source.isSome) do
    throw <| IO.userError "Imported example lost its proof audit or source metadata"
  let some fold := index.find? (·.name == `Examples.ConstantFolding.fold)
    | throw <| IO.userError "Imported API annotation was lost"
  let contracts := #[
    `Examples.ConstantFolding.fold_idempotent,
    `Examples.ConstantFolding.fold_never_grows,
    `Examples.ConstantFolding.fold_preserves_meaning
  ]
  let mentions := #[
    `Examples.ConstantFolding.fold_idempotent,
    `Examples.ConstantFolding.fold_nested_literals,
    `Examples.ConstantFolding.fold_never_grows,
    `Examples.ConstantFolding.fold_preserves_meaning,
    `Examples.ConstantFolding.fold_with_variable
  ]
  unless fold.annotated == contracts && fold.mentioned == mentions do
    throw <| IO.userError "Optimizer contracts did not survive imports"
  let some eval := index.find? (·.name == `Examples.ConstantFolding.eval)
    | throw <| IO.userError "Imported evaluator API was lost"
  unless eval.annotated == eval.mentioned && eval.mentioned.size == 2 do
    throw <| IO.userError "Evaluator contracts did not survive imports"
  unless (← IO.ofExcept workplan.getArr?).isEmpty do
    throw <| IO.userError "Proved self-manifest contracts must leave no unfinished work"
  let report := Json.arr (examples.map Report.entryToJson)
  let path : System.FilePath := "/tmp/lean-manifests-example.json"
  IO.FS.writeFile path report.pretty
  let reread ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let result ← IO.ofExcept <| LatexRoundtrip.check
    "\\manifestThm{Examples.ConstantFolding.fold_preserves_meaning}" reread
  unless result.resolved.size == 1 && result.unresolved.isEmpty do
    throw <| IO.userError "Generated report did not resolve its own theorem marker"
  let texPath := "/tmp/lean-manifests-example.tex"
  IO.FS.writeFile texPath "\\manifestThm{Examples.ConstantFolding.fold_preserves_meaning}"
  let valid ← IO.Process.output {
    cmd := "lean"
    args := #["--run", "Scripts/LatexRoundtripCLI.lean", texPath, path.toString]
  }
  unless valid.exitCode == 0 do
    throw <| IO.userError s!"LaTeX CLI rejected its generated report: {valid.stderr}"
  IO.FS.writeFile texPath "\\manifestThm{Examples.missing}"
  let missing ← IO.Process.output {
    cmd := "lean"
    args := #["--run", "Scripts/LatexRoundtripCLI.lean", texPath, path.toString]
  }
  unless missing.exitCode == 1 do
    throw <| IO.userError "LaTeX CLI did not fail for an unknown manifest name"
  let usage ← IO.Process.output {
    cmd := "lean"
    args := #["--run", "Scripts/LatexRoundtripCLI.lean"]
  }
  unless usage.exitCode == 2 do
    throw <| IO.userError "LaTeX CLI did not report invalid arguments"
  IO.FS.removeFile texPath
  IO.println s!"Checked 13 self-manifest proofs, 5 example proofs, and 2 finite tests; report: {path}"

end Scripts.ReportSmoke

def main : IO Unit := Scripts.ReportSmoke.run
