module

public import LeanEvidence.Spec

public section

open Lean

/-!
# LeanEvidence

The audit's verdict means what `LeanEvidence.Spec` says. Not claimed: that the facts
the audit reads from compiled modules are complete; that extraction is tested, not proved.
-/

namespace LeanEvidence

def Project.check (project : Project) (catalog : Array Name) (inventory : Inventory) : Bool :=
  sorry

def level (premises : Array Premise) : Level := sorry

/-- Every module the build compiles has a role and was inspected. -/
theorem classification_complete (project : Project) (catalog : Array Name)
    (inventory : Inventory) (accepted : project.check catalog inventory = true) :
    ∀ name ∈ catalog, (project.role? name).isSome = true ∧
      ∃ fact ∈ inventory.modules, fact.name = name := by
  sorry

/-- No chain of runtime imports leads from spec, boundary, or core code to the shell
or to tooling. -/
theorem layering_sound (project : Project) (catalog : Array Name) (inventory : Inventory)
    (accepted : project.check catalog inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    (∀ reached, project.role? target = some reached → reached.Inner) ∧
      (project.role? target = none → project.Trusted target) := by
  sorry

/-- Spec and core code is pure, boundary code is foreign, and nothing uses a
nonstandard axiom. -/
theorem purity_sound (project : Project) (catalog : Array Name) (inventory : Inventory)
    (accepted : project.check catalog inventory = true) :
    ∀ fact ∈ inventory.declarations, fact.Standard ∧
      ∀ role, project.role? fact.moduleName = some role → fact.computational = true →
        (role = .spec ∨ role = .core → fact.Pure) ∧ (role = .boundary → fact.external = true) := by
  sorry

/-- A headline is reported proved exactly when its open conjectures are all proved. -/
theorem level_proved_iff (premises : Array Premise) :
    level premises = .proved ↔ ∀ premise ∈ premises, premise.Settled := by
  sorry

end LeanEvidence
