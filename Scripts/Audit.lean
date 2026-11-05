module

public meta import LeanEvidence.Audit

public section
meta section

open LeanEvidence

def main (args : List String) : IO Unit :=
  Audit.run {
    layers := #[(`LeanEvidence, .tooling), (`LeanEvidence.Policy, .core), (`Examples, .tooling),
      (`Examples.ConstantFolding.Spec, .spec), (`Examples.ConstantFolding.Boundary, .boundary),
      (`Examples.ConstantFolding.Core, .core), (`Examples.ConstantFolding.Shell, .shell)]
  } (args.toArray.map String.toName)
