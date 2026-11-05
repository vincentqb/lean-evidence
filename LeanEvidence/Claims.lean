module

public import LeanEvidence.Policy

public section

open Lean

namespace LeanEvidence

private theorem permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  unfold Role.Inner at *
  rcases inner with rfl | rfl | rfl <;> cases target <;> simp_all [Role.permits]

private theorem accepted_parts {project : Project} {catalog : Array Name} {inventory : Inventory}
    (accepted : project.check catalog inventory = true) :
    (∀ name ∈ catalog, (project.role? name).isSome = true ∧
      ∃ fact ∈ inventory.modules, fact.name = name) ∧
    (∀ fact ∈ inventory.modules, project.moduleAdmitted fact = true) ∧
    (∀ fact ∈ inventory.declarations, ∃ role, project.role? fact.moduleName = some role ∧
      fact.admitted role = true) := by
  simp only [Project.check, Bool.and_eq_true, Array.all_eq_true', Array.any_eq_true',
    beq_iff_eq] at accepted
  obtain ⟨⟨⟨_, catalogued⟩, modules⟩, declarations⟩ := accepted
  refine ⟨catalogued, modules, fun fact member => ?_⟩
  have admitted := declarations fact member
  cases owner : project.role? fact.moduleName with
  | none => simp [owner] at admitted
  | some role => exact ⟨role, rfl, by simpa [owner] using admitted⟩

private theorem source_classified {project : Project} {catalog : Array Name}
    {inventory : Inventory} (accepted : project.check catalog inventory = true)
    {source target : Name} (edge : inventory.RuntimeImport source target) :
    ∃ role, project.role? source = some role := by
  obtain ⟨fact, member, named, _⟩ := edge
  have admitted := (accepted_parts accepted).2.1 fact member
  unfold Project.moduleAdmitted at admitted
  cases owner : project.role? fact.name with
  | none => simp [owner] at admitted
  | some role => exact ⟨role, named ▸ owner⟩

private theorem import_step {project : Project} {catalog : Array Name} {inventory : Inventory}
    (accepted : project.check catalog inventory = true) {source target : Name} {role : Role}
    (classified : project.role? source = some role) (inner : role.Inner)
    (edge : inventory.RuntimeImport source target) :
    (∀ reached, project.role? target = some reached → reached.Inner) ∧
      (project.role? target = none → project.Trusted target) := by
  obtain ⟨fact, member, named, dependency, imported, target_eq, runtime⟩ := edge
  have admitted := (accepted_parts accepted).2.1 fact member
  simp only [Project.moduleAdmitted, named, classified, Bool.and_eq_true,
    Array.all_eq_true'] at admitted
  have permitted := admitted.2 dependency imported
  simp only [Project.admits, runtime, target_eq, Bool.false_or] at permitted
  constructor
  · intro reached owner
    simp only [owner] at permitted
    exact permits_inner permitted inner
  · intro owner
    simp only [owner, Project.trusts] at permitted
    exact Array.any_eq_true'.mp permitted

theorem classification_complete (project : Project) (catalog : Array Name)
    (inventory : Inventory) (accepted : project.check catalog inventory = true) :
    ∀ name ∈ catalog, (project.role? name).isSome = true ∧
      ∃ fact ∈ inventory.modules, fact.name = name :=
  (accepted_parts accepted).1

theorem layering_sound (project : Project) (catalog : Array Name) (inventory : Inventory)
    (accepted : project.check catalog inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    (∀ reached, project.role? target = some reached → reached.Inner) ∧
      (project.role? target = none → project.Trusted target) := by
  induction reaches with
  | single edge => exact import_step accepted classified inner edge
  | tail _ edge previous =>
    obtain ⟨middle, owner⟩ := source_classified accepted edge
    exact import_step accepted owner (previous.1 middle owner) edge

theorem purity_sound (project : Project) (catalog : Array Name) (inventory : Inventory)
    (accepted : project.check catalog inventory = true) :
    ∀ fact ∈ inventory.declarations, fact.Standard ∧
      ∀ role, project.role? fact.moduleName = some role → fact.computational = true →
        (role = .spec ∨ role = .core → fact.Pure) ∧ (role = .boundary → fact.external = true) := by
  intro fact member
  obtain ⟨owner, classified, admitted⟩ := (accepted_parts accepted).2.2 fact member
  simp only [DeclarationFact.admitted, DeclarationFact.standard, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Array.all_eq_true', Array.contains_iff_mem] at admitted
  obtain ⟨standard, behaviour⟩ := admitted
  refine ⟨standard, fun role assigned runs => ?_⟩
  rw [classified] at assigned
  cases assigned
  rcases behaviour with stub | checked
  · simp [runs] at stub
  · cases owner <;>
      simp_all [DeclarationFact.pure, DeclarationFact.Pure, Array.isEmpty_iff]

theorem level_proved_iff (premises : Array Premise) :
    level premises = .proved ↔ ∀ premise ∈ premises, premise.Settled := by
  unfold level Premise.Settled
  split
  · rename_i settled
    simp only [Array.all_eq_true', Bool.or_eq_true, beq_iff_eq] at settled
    simpa using settled
  · rename_i unsettled
    simp only [Array.all_eq_true', Bool.or_eq_true, beq_iff_eq] at unsettled
    simpa using unsettled

end LeanEvidence
