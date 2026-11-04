module

public meta import Lean

public section
meta section

open Lean

namespace LeanManifests.LatexRoundtrip

structure Markers where
  thmRefs : Array String := #[]
  symRefs : Array (String × String) := #[]
  deriving Inhabited, Repr

private partial def readGroup (chars : List Char) (depth : Nat := 1)
    (acc : List Char := []) : Except String (String × List Char) :=
  match chars with
  | [] => .error "Unclosed marker argument"
  | '\\' :: c :: rest => readGroup rest depth (c :: '\\' :: acc)
  | '}' :: rest =>
    if depth == 1 then .ok (String.ofList acc.reverse, rest)
    else readGroup rest (depth - 1) ('}' :: acc)
  | '{' :: rest => readGroup rest (depth + 1) ('{' :: acc)
  | c :: rest => readGroup rest depth (c :: acc)

private def argument (command : String) (chars : List Char) :
    Except String (String × List Char) :=
  match chars.dropWhile Char.isWhitespace with
  | '{' :: rest => readGroup rest
  | _ => .error s!"\\{command} requires a braced argument"

private partial def scan (chars : List Char) (result : Markers) : Except String Markers := do
  match chars with
  | [] => return result
  | '%' :: rest => scan (rest.dropWhile (· != '\n')) result
  | '\\' :: rest =>
    let (letters, remaining) := rest.span Char.isAlpha
    let command := String.ofList letters
    if command == "manifestThm" || command == "manifestSym" then
      let (rawName, remaining) ← argument command remaining
      let name := rawName.trimAscii.toString
      if name.isEmpty then throw s!"\\{command} has an empty manifest name"
      if command == "manifestThm" then
        scan remaining { result with thmRefs := result.thmRefs.push name }
      else
        let (symbol, remaining) ← argument command remaining
        scan remaining { result with symRefs := result.symRefs.push (name, symbol) }
    else if letters.isEmpty then
      scan remaining.tail result
    else
      scan remaining result
  | _ :: rest => scan rest result

def parseMarkers (text : String) : Except String Markers :=
  scan text.toList {}

structure Result where
  resolved : Array String
  unresolved : Array String
  unreferenced : Array String
  deriving Repr

private def sorted (names : Std.HashSet String) : Array String :=
  names.toArray.qsort (· < ·)

def check (text : String) (report : Json) : Except String Result := do
  let entries ← report.getArr?
  let mut known : Std.HashSet String := {}
  for entry in entries do
    let name ← entry.getObjValAs? String "name"
    if name.isEmpty then throw "The report contains an empty manifest name"
    if known.contains name then throw s!"Duplicate manifest name in report: {name}"
    known := known.insert name
  let markers ← parseMarkers text
  let referenced := (markers.thmRefs ++ markers.symRefs.map Prod.fst).foldl
    (fun names name => names.insert name) ({} : Std.HashSet String)
  return {
    resolved := sorted (referenced.filter known.contains)
    unresolved := sorted (referenced.filter (!known.contains ·))
    unreferenced := sorted (known.filter (!referenced.contains ·))
  }

def run (texPath reportPath : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile texPath
  let report ← IO.ofExcept <| Json.parse (← IO.FS.readFile reportPath)
  let result ← IO.ofExcept <| check text report
  IO.println s!"Resolved {result.resolved.size} manifest names; {result.unreferenced.size} report entries are unreferenced."
  unless result.unresolved.isEmpty do
    throw <| IO.userError ("Unresolved manifest names: " ++
      String.intercalate ", " result.unresolved.toList)

end LeanManifests.LatexRoundtrip
