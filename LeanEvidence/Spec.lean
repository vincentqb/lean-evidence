module

public import Lean.Data.Name

public section

open Lean

namespace LeanEvidence

/-- Where a module sits: `spec` and `boundary` are human-owned, `core` is proved,
`shell` performs effects, `tooling` runs at compile time. -/
inductive Role where
  | spec | boundary | core | shell | tooling
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

/-- Roles whose runtime code must never reach the shell or tooling. -/
@[expose] def Role.Inner (role : Role) : Prop :=
  role = .spec ∨ role = .boundary ∨ role = .core

/-- Module prefixes and their roles, external packages trusted as-is, and builtins
whose side effects the core may not use. -/
structure Project where
  layers : Array (Name × Role)
  trusted : Array Name := #[`Init, `Std, `Lean, `Lake]
  forbidden : Array Name := #[``dbgTrace, ``dbgTraceIfShared, ``dbgSleep]
  deriving Inhabited, Repr

/-- The role of a module is the role of its longest classified prefix. -/
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

/-- `source` imports `target` for use at run time. -/
@[expose] def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

@[expose] def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The code that runs is the code Lean checked: no escape hatch, effect, or initializer. -/
@[expose] def DeclarationFact.Pure (fact : DeclarationFact) : Prop :=
  fact.isUnsafe = false ∧ fact.isPartial = false ∧ fact.external = false ∧
    fact.replaced = false ∧ fact.initializes = false ∧ fact.effects = false ∧
    fact.forbidden = #[]

@[expose] def DeclarationFact.Standard (fact : DeclarationFact) : Prop :=
  ∀ ax ∈ fact.axioms, ax ∈ standardAxioms

inductive ClaimKind where
  | world | conjecture
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

/-- A hypothesis of a headline theorem that names a registered claim. -/
structure Premise where
  claim : Name
  kind : ClaimKind
  discharged : Bool := false
  deriving Inhabited, Repr

/-- A world assumption stays a premise; a conjecture is settled once proved. -/
@[expose] def Premise.Settled (premise : Premise) : Prop :=
  premise.kind = .world ∨ premise.discharged = true

inductive Level where
  | proved | derived
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited, Repr

end LeanEvidence
