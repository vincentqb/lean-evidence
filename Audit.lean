module

public meta import SoftwareChallenge.Audit

public meta def main : List String → IO Unit := SoftwareChallenge.Audit.run {
  layers := #[(`SoftwareChallenge, .tooling), (`SoftwareChallenge.Policy, .core), (`Examples, .tooling),
    (`Examples.ConstantFolding.Spec, .spec), (`Examples.ConstantFolding.Boundary, .boundary),
    (`Examples.ConstantFolding.Core, .core), (`Examples.ConstantFolding.Shell, .shell)] }
