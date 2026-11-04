module

public import LeanEvidence.Evidence

public section

open Lean

namespace LeanEvidence

universe u

@[expose] def Contract {α : Sort u} (implementation : α) (specification : α → Prop) : Prop :=
  specification implementation

inductive Role where
  | core | adapter | foreign | tooling
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

@[expose] def Role.permits : Role → Role → Bool
  | .tooling, _ => true
  | _, .core => true
  | .adapter, .adapter | .adapter, .foreign | .foreign, .foreign => true
  | _, _ => false

def Role.Allows (source target : Role) : Prop :=
  source = .tooling ∨ target = .core ∨
    (source = .adapter ∧ (target = .adapter ∨ target = .foreign)) ∨
    (source = .foreign ∧ target = .foreign)

structure ModuleRule where
  name : Name
  role : Role
  deriving Inhabited, Repr

structure Project where
  modules : Array ModuleRule
  trusted : Array Name := #[`Init, `Std, `Lean, `Lake]
  deriving Inhabited, Repr

@[expose] def Project.role? (project : Project) (name : Name) : Option Role :=
  (project.modules.find? (·.name == name)).map (·.role)

@[expose] def Project.isTrusted (project : Project) (name : Name) : Bool :=
  project.trusted.any (·.isPrefixOf name)

@[expose] def Project.permits (project : Project) (source : Role) (target : Name)
    (comptime : Bool) : Bool :=
  match project.role? target with
  | some role => comptime || source.permits role
  | none => project.isTrusted target

def Project.Allows (project : Project) (source : Role) (target : Name)
    (comptime : Bool) : Prop :=
  match project.role? target with
  | some role => comptime = true ∨ source.Allows role
  | none => ∃ root ∈ project.trusted, root.isPrefixOf target = true

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
  comptime : Bool := false
  isUnsafe : Bool := false
  isPartial : Bool := false
  effects : Bool := false
  initializes : Bool := false
  external : Bool := false
  foreignEvidence : Bool := false
  missingBody : Bool := false
  axioms : Array Name := #[]
  conformance : Bool := false
  runtimeAxioms : Array Name := #[]
  needsContract : Bool := false
  hasContract : Bool := false
  dependencies : Array Name := #[]
  deriving Inhabited, Repr

@[expose] def DeclarationFact.check (project : Project) (role : Role)
    (fact : DeclarationFact) : Bool :=
  fact.axioms.all (fun ax =>
    standardAxioms.contains ax || (fact.conformance && fact.runtimeAxioms.contains ax)) &&
    (!fact.conformance || role != .core) &&
    (!fact.needsContract || fact.hasContract) &&
    (!fact.external || (role == .foreign && fact.foreignEvidence) ||
      (role == .tooling && fact.comptime)) &&
    (!fact.computational ||
      ((!fact.missingBody || fact.external) &&
        (role == .tooling ||
          ((!fact.isUnsafe && !fact.isPartial) || (fact.external && fact.foreignEvidence))) &&
        (role != .core || (!fact.effects && !fact.initializes && !fact.external)) &&
        (role != .tooling || fact.comptime) &&
        fact.dependencies.all (fun target => project.permits role target false)))

def DeclarationFact.Compliant (project : Project) (role : Role)
    (fact : DeclarationFact) : Prop :=
  (∀ ax ∈ fact.axioms, ax ∈ standardAxioms ∨
    (fact.conformance = true ∧ ax ∈ fact.runtimeAxioms)) ∧
  (fact.conformance = true → role ≠ .core) ∧
  (fact.needsContract = true → fact.hasContract = true) ∧
  (fact.external = true →
    (role = .foreign ∧ fact.foreignEvidence = true) ∨
      (role = .tooling ∧ fact.comptime = true)) ∧
  (fact.computational = true →
    (fact.missingBody = true → fact.external = true) ∧
    (role = .tooling ∨
      (fact.isUnsafe = false ∧ fact.isPartial = false) ∨
      (fact.external = true ∧ fact.foreignEvidence = true)) ∧
    (role = .core → fact.effects = false ∧ fact.initializes = false ∧ fact.external = false) ∧
    (role = .tooling → fact.comptime = true) ∧
    (∀ target ∈ fact.dependencies, project.Allows role target false))

@[expose] def ModuleFact.check (project : Project) (fact : ModuleFact) : Bool :=
  match project.role? fact.name with
  | none => false
  | some role =>
    fact.usesModuleSystem &&
      fact.imports.all (fun dependency =>
        project.permits role dependency.name dependency.comptime)

def ModuleFact.Compliant (project : Project) (fact : ModuleFact) : Prop :=
  ∃ role, project.role? fact.name = some role ∧ fact.usesModuleSystem = true ∧
    ∀ dependency ∈ fact.imports,
      project.Allows role dependency.name dependency.comptime

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact
  deriving Inhabited, Repr

@[expose] def Project.check (project : Project) (catalog : Array Name)
    (inventory : Inventory) : Bool :=
  decide (project.modules.toList.map (·.name)).Nodup &&
    catalog.all (fun name => (project.role? name).isSome) &&
    project.modules.all (fun rule => catalog.contains rule.name) &&
    catalog.all (fun name => inventory.modules.any (·.name == name)) &&
    inventory.modules.all (·.check project) &&
    inventory.declarations.all (fun fact =>
      match project.role? fact.moduleName with
      | none => false
      | some role => fact.check project role)

def Project.Compliant (project : Project) (catalog : Array Name)
    (inventory : Inventory) : Prop :=
  (project.modules.toList.map (·.name)).Nodup ∧
  (∀ name ∈ catalog, (project.role? name).isSome = true) ∧
  (∀ rule ∈ project.modules, rule.name ∈ catalog) ∧
  (∀ name ∈ catalog, ∃ fact ∈ inventory.modules, fact.name = name) ∧
  (∀ fact ∈ inventory.modules, fact.Compliant project) ∧
  (∀ fact ∈ inventory.declarations,
    ∃ role, project.role? fact.moduleName = some role ∧ fact.Compliant project role)

end LeanEvidence
