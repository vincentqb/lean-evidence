module

public meta import LeanEvidence.Audit

public meta def main : List String → IO Unit := LeanEvidence.Audit.run {
  layers := #[(`LeanEvidence, .tooling), (`LeanEvidence.Policy, .core), (`Examples, .tooling),
    (`Examples.ConstantFolding.Spec, .spec), (`Examples.ConstantFolding.Boundary, .boundary),
    (`Examples.ConstantFolding.Core, .core), (`Examples.ConstantFolding.Shell, .shell)] }
