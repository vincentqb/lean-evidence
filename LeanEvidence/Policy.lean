module

public import Lean.Data.Name

public section

open Lean

namespace LeanEvidence

inductive Role where
  | spec | boundary | core | shell | tooling
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

@[expose] def Role.Inner (role : Role) : Prop :=
  role = .spec ∨ role = .boundary ∨ role = .core

structure Project where
  layers : Array (Name × Role)
  trusted : Array Name := #[`Init, `Std, `Lean, `Lake]
  forbidden : Array Name := #[``dbgTrace, ``dbgTraceIfShared, ``dbgSleep]
  deriving Inhabited, Repr

@[expose] def Project.role? (project : Project) (name : Name) : Option Role :=
  (project.layers.foldl (init := none) fun best (layer, role) =>
    if layer.isPrefixOf name && best.all (·.1.getNumParts < layer.getNumParts) then
      some (layer, role)
    else best).map (·.2)

@[expose] def Project.Trusted (project : Project) (name : Name) : Prop :=
  ∃ root ∈ project.trusted, root.isPrefixOf name = true

structure ImportFact where
  name : Name
  comptime : Bool
  deriving Inhabited, Repr

structure ModuleFact where
  name : Name
  usesModuleSystem : Bool
  imports : Array ImportFact := #[]
  deriving Inhabited, Repr

structure DeclarationFact where
  name : Name
  moduleName : Name
  computational : Bool := true
  isUnsafe : Bool := false
  isPartial : Bool := false
  external : Bool := false
  replaced : Bool := false
  initializes : Bool := false
  effects : Bool := false
  forbidden : Array Name := #[]
  axioms : Array Name := #[]
  deriving Inhabited, Repr

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact
  deriving Inhabited, Repr

@[expose] def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

@[expose] def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

inductive ClaimKind where
  | world | conjecture
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

structure Premise where
  claim : Name
  kind : ClaimKind
  discharged : Bool := false
  deriving Inhabited, Repr

inductive Level where
  | proved | derived
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

@[expose] def Role.permits : Role → Role → Bool
  | .tooling, _ => true
  | .shell, target => target != .tooling
  | source, target => target == .spec || target == .boundary || target == source

@[expose] def Project.trusts (project : Project) (name : Name) : Bool :=
  project.trusted.any (·.isPrefixOf name)

@[expose] def Project.admits (project : Project) (source : Role) (dependency : ImportFact) : Bool :=
  dependency.comptime || match project.role? dependency.name with
    | some target => source.permits target
    | none => project.trusts dependency.name

@[expose] def Project.moduleAdmitted (project : Project) (fact : ModuleFact) : Bool :=
  match project.role? fact.name with
  | some role => fact.usesModuleSystem && fact.imports.all (project.admits role)
  | none => false

@[expose] def DeclarationFact.pure (fact : DeclarationFact) : Bool :=
  !fact.isUnsafe && !fact.isPartial && !fact.external && !fact.replaced &&
    !fact.initializes && !fact.effects && fact.forbidden.isEmpty

@[expose] def DeclarationFact.standard (fact : DeclarationFact) : Bool :=
  fact.axioms.all standardAxioms.contains

@[expose] def DeclarationFact.admitted (role : Role) (fact : DeclarationFact) : Bool :=
  fact.standard && (!fact.computational || match role with
    | .spec | .core => fact.pure
    | .boundary => fact.external
    | .shell => !fact.isUnsafe && !fact.external && !fact.replaced
    | .tooling => true)

@[expose] def Project.check (project : Project) (catalog : Array Name) (inventory : Inventory) :
    Bool :=
  decide (project.layers.toList.map (·.1)).Nodup &&
    catalog.all (fun name =>
      (project.role? name).isSome && inventory.modules.any (·.name == name)) &&
    inventory.modules.all project.moduleAdmitted &&
    inventory.declarations.all fun fact =>
      match project.role? fact.moduleName with
      | some role => fact.admitted role
      | none => false

@[expose] def level (premises : Array Premise) : Level :=
  if premises.all (fun premise => premise.kind == .world || premise.discharged) then .proved
  else .derived

private theorem permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  unfold Role.Inner at *
  rcases inner with rfl | rfl | rfl <;> cases target <;> simp_all [Role.permits]

private theorem modules_admitted {project : Project} {catalog : Array Name}
    {inventory : Inventory} (accepted : project.check catalog inventory = true) :
    ∀ fact ∈ inventory.modules, project.moduleAdmitted fact = true := by
  simp only [Project.check, Bool.and_eq_true, Array.all_eq_true'] at accepted
  exact accepted.1.2

private theorem source_classified {project : Project} {catalog : Array Name}
    {inventory : Inventory} (accepted : project.check catalog inventory = true)
    {source target : Name} (edge : inventory.RuntimeImport source target) :
    ∃ role, project.role? source = some role := by
  obtain ⟨fact, member, named, _⟩ := edge
  have admitted := modules_admitted accepted fact member
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
  have admitted := modules_admitted accepted fact member
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

/-- Once the audit accepts, no chain of runtime imports leads from spec, boundary, or
core code to the shell or to tooling. -/
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

end LeanEvidence
