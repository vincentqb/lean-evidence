module

public meta import LeanEvidence.Report

public section
meta section

open Lean

namespace LeanEvidence.IndexGen

structure ApiEntry where
  name : Name
  annotated : Array Name
  mentioned : Array Name
  deriving Repr

def buildIndex (scope : Name) : CoreM (Array ApiEntry) := do
  let env ← getEnv
  let entries ← Report.collectEntries scope
  let mut links : Std.HashMap Name ApiEntry := {}
  for (n, claims) in (theoremsExtension.getState env).toArray do
    if scope.isPrefixOf n then
      links := links.insert n { name := n, annotated := claims, mentioned := #[] }
  for entry in entries do
    let info ← getConstInfo entry.name
    for n in info.type.getUsedConstants do
      if !scope.isPrefixOf n then continue
      let some functionInfo := env.find? n | continue
      unless functionInfo matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do continue
      if ← Meta.MetaM.run' (Meta.isProp functionInfo.type) then continue
      let previous := (links[n]?).getD { name := n, annotated := #[], mentioned := #[] }
      unless previous.mentioned.contains entry.name do
        links := links.insert n { previous with mentioned := previous.mentioned.push entry.name }
  return links.toArray.map Prod.snd |>.map (fun e => {
    e with
    annotated := e.annotated.qsort (fun a b => a.toString < b.toString)
    mentioned := e.mentioned.qsort (fun a b => a.toString < b.toString)
  }) |>.qsort (fun a b => a.name.toString < b.name.toString)

private def claimLabel (env : Environment) (n : Name) : String :=
  let label := (getEvidence? env n).map (toString ∘ Evidence.kind) |>.getD "unknown"
  s!"`{n}` ({label})"

def renderMarkdown (entries : Array ApiEntry) : CoreM String := do
  let env ← getEnv
  let mut lines := #[
    "# API and registered claims", "",
    "Annotations are author-supplied links. Mentions are occurrences in claim types.", ""
  ]
  for entry in entries do
    lines := lines.push s!"## `{entry.name}`" |>.push ""
    if !entry.annotated.isEmpty then
      lines := lines.push ("Annotated: " ++
        String.intercalate ", " (entry.annotated.map (claimLabel env)).toList ++ ".") |>.push ""
    if !entry.mentioned.isEmpty then
      lines := lines.push ("Mentioned by: " ++
        String.intercalate ", " (entry.mentioned.map (claimLabel env)).toList ++ ".") |>.push ""
  return String.intercalate "\n" lines.toList

def run (scope : Name) (outPath : System.FilePath) (imports : Array Import) : IO Unit := do
  let markdown ← Report.withEnvironment imports do
    renderMarkdown (← buildIndex scope)
  IO.FS.writeFile outPath markdown

end LeanEvidence.IndexGen
