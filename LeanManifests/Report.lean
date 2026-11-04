module

public meta import LeanManifests.Basic

public section
meta section

open Lean

namespace LeanManifests.Report

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
    | throwError "{n} has no manifest evidence"
  let info ← getConstInfo n
  if evidence.kind.requiresProof then requireProof n
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

def withEnvironment {α : Type} (imports : Array Import) (action : CoreM α) : IO α := do
  if imports.isEmpty then throw <| IO.userError "Supply at least one compiled module to report on"
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules imports {} (loadExts := true) (level := .server)
  let (result, _) ← action.toIO
    { fileName := "<manifest-report>", fileMap := default } { env }
  return result

def run (scope : Name) (outPath : System.FilePath) (imports : Array Import) : IO Unit := do
  let entries ← withEnvironment imports (collectEntries scope)
  IO.FS.writeFile outPath (Json.arr (entries.map entryToJson)).pretty
  IO.println s!"Wrote {entries.size} manifest entries to {outPath}"

end LeanManifests.Report
