module

public import Tests.Fixtures.Core
public import Tests.Fixtures.Foreign
public import Tests.Fixtures.Adapter
public import Tests.Fixtures.Rejected
import all Tests.Fixtures.Core
import all Tests.Fixtures.Foreign
import all Tests.Fixtures.Adapter
import all Tests.Fixtures.Rejected
public meta import Tests.Fixtures.Rejected
meta import LeanEvidence.Audit
meta import Tests.Support

public section
meta section

open Lean LeanEvidence

namespace Tests.Policy

private def project : Project := {
  modules := #[
    ⟨`Tests.Fixtures.Core, .core⟩,
    ⟨`Tests.Fixtures.Foreign, .foreign⟩,
    ⟨`Tests.Fixtures.Adapter, .adapter⟩
  ]
  trusted := #[`Init, `Std, `Lean, `LeanEvidence]
}

rejects "is false" in
  /-- A deliberately wrong native binding must fail even though its Lean body agrees. -/
  ConformanceFixture wrong_successor :
    Fixtures.Rejected.wrongSuccessor 0 = Fixtures.Core.successor 0

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def expectViolation (errors : Array String) (name reason : String) : CoreM Unit := do
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection for {name}: {reason}\n{errors}"

run_cmd Lean.Elab.Command.liftCoreM do
  let catalog := project.modules.map (·.name)
  let accepted ← Audit.check project catalog
  unless accepted.declarations.any (fun fact =>
      fact.name == `Tests.Fixtures.Core.successor && fact.needsContract && fact.hasContract) do
    throwError "The compiled public core operation lost its contract"
  unless accepted.declarations.any (fun fact =>
      privateToUserName fact.name == `Tests.Fixtures.Foreign.replacement &&
        fact.external && fact.foreignEvidence) do
    throwError "The private compiled replacement lost its foreign evidence"
  let imported ← Audit.inspect project catalog
  unless imported.declarations.any (fun fact =>
      privateToUserName fact.name == `Tests.Fixtures.Foreign.replacement &&
        fact.external && fact.foreignEvidence) do
    throwError "Importing compiled modules lost downstream foreign evidence"
  let rejectedProject := { project with
    modules := project.modules.push ⟨`Tests.Fixtures.Rejected, .core⟩ }
  let rejectedCatalog := catalog.push `Tests.Fixtures.Rejected
  let importedRejected ← Report.withEnvironment #[{ module := `Tests.Fixtures.Rejected }]
    (Audit.collect rejectedProject rejectedCatalog)
  expectViolation (Audit.violations rejectedProject rejectedCatalog importedRejected)
    "uncovered" "missing Contract"
  let rejected ← Audit.collect rejectedProject rejectedCatalog
  let errors := Audit.violations rejectedProject rejectedCatalog rejected
  unless !rejectedProject.check rejectedCatalog rejected do
    throwError "An invalid compiled core passed the project check"
  for (name, reason) in #[
      ("uncovered", "missing Contract"), ("hiddenUnsafe", "unsafe or partial"),
      ("diverging", "unsafe or partial"), ("hiddenEffect", "effects in core"),
      ("packagedEffect", "effects in core"),
      ("EffectBox.ofNat", "missing Contract"),
      ("startup", "effects in core"), ("unregistered", "unregistered foreign"),
      ("Rejected.raw", "nonstandard axioms"), ("Rejected.hole", "nonstandard axioms"),
      ("spoof._unsafe_rec", "missing Contract"), ("redirected", "forbidden dependencies")] do
    expectViolation errors name reason
  let tooling := { project with
    modules := project.modules.push ⟨`Tests.Fixtures.Rejected, .tooling⟩ }
  let toolingInventory ← Audit.collect tooling rejectedCatalog
  expectViolation (Audit.violations tooling rejectedCatalog toolingInventory)
    "runtimeHelper" "runtime code in tooling"
  unless !(project.check (catalog.push `Tests.Fixtures.Rejected) accepted) &&
      !({ project with modules := project.modules.push ⟨`Unused, .core⟩ }.check catalog accepted) &&
      !({ project with modules := project.modules ++ project.modules }.check catalog accepted) do
    throwError "Missing, stale, or duplicate module classifications passed"
  unless !(ModuleFact.check project { name := `Tests.Fixtures.Core, usesModuleSystem := false }) do
    throwError "A module outside the modern module system passed"

rejects "requires extern or implemented_by" in
  ForeignBinding Fixtures.Core.successor models Fixtures.Core.successor
    assumes Fixtures.Foreign.successor_agrees conforms Fixtures.Foreign.successor_cases

rejects "already registered" in
  ForeignBinding Fixtures.Foreign.successor models Fixtures.Core.successor
    assumes Fixtures.Foreign.successor_agrees conforms Fixtures.Foreign.successor_cases

/-- A deliberately unrelated assumption for testing foreign evidence linkage. -/
WorldClaim unrelated := 0 = 0

rejects "pointwise equality" in
  ForeignBinding Fixtures.Rejected.unregistered models Fixtures.Core.successor
    assumes unrelated conforms Fixtures.Foreign.successor_cases

/-- Smaller outputs falsify this deliberately insufficient assumption. -/
WorldClaim insufficient := ∀ n, n < Fixtures.Rejected.unregistered n ∧
  n < Fixtures.Core.successor n

rejects "pointwise equality" in
  ForeignBinding Fixtures.Rejected.unregistered models Fixtures.Core.successor
    assumes insufficient conforms Fixtures.Foreign.successor_cases

/-- A differing native result falsifies agreement with the Lean model. -/
WorldClaim unregistered_agrees := ∀ n,
  Fixtures.Rejected.unregistered n = Fixtures.Core.successor n

/-- This deliberately weak fixture passes without checking the comparison. -/
ConformanceFixture insufficient_cases :
  Fixtures.Rejected.unregistered 0 = Fixtures.Core.successor 0 ∨ True

rejects "compare the binding and model" in
  ForeignBinding Fixtures.Rejected.unregistered models Fixtures.Core.successor
    assumes unregistered_agrees conforms insufficient_cases

rejects "nonstandard axioms" in
  ProvenTheorem fixture_is_not_a_kernel_proof :
      Fixtures.Foreign.successor 0 = Fixtures.Core.successor 0 ∧
        Fixtures.Foreign.successor 41 = Fixtures.Core.successor 41 :=
    Fixtures.Foreign.successor_cases

end Tests.Policy
