module

public meta import LeanEvidence.Audit

public section
meta section

open Lean LeanEvidence

namespace LeanEvidenceAudit

def project : Project := {
  layers := #[
    (`LeanEvidence, .tooling),
    (`LeanEvidence.Spec, .spec),
    (`LeanEvidence.Policy, .core),
    (`Examples, .tooling),
    (`Examples.ConstantFolding.Spec, .spec),
    (`Examples.ConstantFolding.Boundary, .boundary),
    (`Examples.ConstantFolding.Core, .core),
    (`Examples.ConstantFolding.Shell, .shell),
    (`LeanEvidenceClaims, .tooling),
    (`LeanEvidenceAudit, .tooling)
  ]
  trusted := #[`Init, `Std, `Lean]
}

end LeanEvidenceAudit

def main (args : List String) : IO Unit :=
  Audit.run LeanEvidenceAudit.project (args.toArray.map String.toName)
