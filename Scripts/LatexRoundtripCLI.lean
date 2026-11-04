module

public meta import LeanManifests.LatexRoundtrip

public section
meta section

def main (args : List String) : IO UInt32 := do
  match args with
  | [texFile, jsonFile] =>
    try
      LeanManifests.LatexRoundtrip.run texFile jsonFile
      return 0
    catch error =>
      IO.eprintln error
      return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run Scripts/LatexRoundtripCLI.lean <tex-file> <json-file>"
    return 2
