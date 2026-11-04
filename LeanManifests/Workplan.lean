module

public meta import LeanManifests.Report

public section
meta section

open Lean

namespace LeanManifests.Workplan

private def complete (env : Environment) (n : Name) : Bool :=
  (getEvidence? env n).any Evidence.isComplete

def collect (scope : Name) : CoreM Json := do
  let env ← getEnv
  let entries ← Report.collectEntries scope
  let mut items := #[]
  for entry in entries do
    if !entry.evidence.needsWork then continue
    let deps := ((getDependsOn? env entry.name).getD #[]).filter (!complete env ·)
    items := items.push <| Json.mkObj [
      ("name", Json.str entry.name.toString),
      ("evidence", Json.str (toString entry.evidence.kind)),
      ("assumptions", Json.arr (entry.evidence.assumptions.map (Json.str ∘ Name.toString))),
      ("blocked_on", Json.arr (deps.map (Json.str ∘ Name.toString))),
      ("entry_point", toJson (isEntryPoint env entry.name && deps.isEmpty)),
      ("estimated_minutes", (getEstimatedMinutes? env entry.name).map toJson |>.getD Json.null)
    ]
  return Json.arr items

def run (scope : Name) (outPath : System.FilePath) (imports : Array Import) : IO Unit := do
  let json ← Report.withEnvironment imports (collect scope)
  IO.FS.writeFile outPath json.pretty

end LeanManifests.Workplan
