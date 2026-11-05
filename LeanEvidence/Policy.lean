module

public import LeanEvidence.Spec

public section

open Lean

namespace LeanEvidence

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

end LeanEvidence
