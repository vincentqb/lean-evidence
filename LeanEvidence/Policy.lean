module

public import Lean.Data.Name

public section

open Lean

namespace LeanEvidence

inductive Role where
  | spec | boundary | core | shell | tooling
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

@[expose] def Role.Inner (role : Role) : Prop :=
  role = .spec ∨ role = .boundary ∨ role = .core

structure Project where
  layers : Array (Name × Role)
  trusted : Array Name := #[`Init, `Std, `Lean]

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

structure ModuleFact where
  name : Name
  usesModuleSystem : Bool
  imports : Array ImportFact

structure DeclarationFact where
  name : Name
  moduleName : Name
  computational : Bool
  isUnsafe : Bool
  isPartial : Bool
  external : Bool
  replaced : Bool
  initializes : Bool
  effects : Bool
  debug : Bool
  axioms : Array Name

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact

@[expose] def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

@[expose] def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

inductive ClaimKind where
  | world | conjecture
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Premise where
  claim : Name
  kind : ClaimKind
  discharged : Bool

@[expose] def proved (premises : Array Premise) : Bool :=
  premises.all fun premise => premise.kind == .world || premise.discharged

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

@[expose] def DeclarationFact.reasons (role : Role) (fact : DeclarationFact) : List String :=
  let flags := [(fact.isUnsafe, "unsafe"), (fact.isPartial, "partial"),
    (fact.external, "@[extern]"), (fact.replaced, "@[implemented_by]"),
    (fact.initializes, "initializer"), (fact.effects, "IO"), (fact.debug, "dbg builtin")]
  let raised := fun (allowed : List String) =>
    flags.filterMap fun (set, reason) => if set && !allowed.contains reason then some reason else none
  (if fact.axioms.isEmpty then [] else [s!"axioms {fact.axioms}"]) ++
    if !fact.computational then [] else match role with
      | .spec | .core => raised []
      | .boundary => if fact.external then [] else ["not an @[extern] binding"]
      | .shell => raised ["partial", "initializer", "IO", "dbg builtin"]
      | .tooling => []

@[expose] def Project.check (project : Project) (inventory : Inventory) : Bool :=
  inventory.modules.all project.moduleAdmitted &&
    inventory.declarations.all fun fact => match project.role? fact.moduleName with
      | some role => (fact.reasons role).isEmpty
      | none => false

private theorem permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  unfold Role.Inner at *
  rcases inner with rfl | rfl | rfl <;> cases target <;> simp_all [Role.permits]

private theorem import_step {project : Project} {inventory : Inventory}
    (accepted : project.check inventory = true) {source target : Name}
    (inner : ∀ role, project.role? source = some role → role.Inner)
    (edge : inventory.RuntimeImport source target) :
    (∀ reached, project.role? target = some reached → reached.Inner) ∧
      (project.role? target = none → project.Trusted target) := by
  obtain ⟨fact, member, named, dependency, imported, target_eq, runtime⟩ := edge
  simp only [Project.check, Bool.and_eq_true, Array.all_eq_true'] at accepted
  have admitted := accepted.1 fact member
  unfold Project.moduleAdmitted at admitted
  rw [named] at admitted
  cases owner : project.role? source with
  | none => simp [owner] at admitted
  | some role =>
    simp only [owner, Bool.and_eq_true, Array.all_eq_true'] at admitted
    have permitted := admitted.2 dependency imported
    simp only [Project.admits, runtime, target_eq, Bool.false_or] at permitted
    constructor
    · intro reached found
      simp only [found] at permitted
      exact permits_inner permitted (inner role owner)
    · intro found
      simp only [found, Project.trusts] at permitted
      exact Array.any_eq_true'.mp permitted

/-- Once the audit accepts, no chain of runtime imports leads from spec, boundary, or
core code to the shell or to tooling. -/
theorem layering_sound (project : Project) (inventory : Inventory)
    (accepted : project.check inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    (∀ reached, project.role? target = some reached → reached.Inner) ∧
      (project.role? target = none → project.Trusted target) := by
  induction reaches with
  | single edge =>
    refine import_step accepted (fun found owner => ?_) edge
    rw [classified] at owner
    cases owner
    exact inner
  | tail _ edge previous => exact import_step accepted previous.1 edge

end LeanEvidence
