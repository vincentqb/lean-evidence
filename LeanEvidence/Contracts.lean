module

public meta import LeanEvidence.Commands
import all LeanEvidence.Evidence
import all LeanEvidence.Policy

public section
meta section

open Lean

namespace LeanEvidence.Contracts

ProvenTheorem standard_axioms_iff : Contract nonstandardAxioms (fun classify =>
    ∀ axioms : Array Name, (classify axioms).isEmpty = true ↔
      ∀ ax ∈ axioms, ax = ``propext ∨ ax = ``Classical.choice ∨ ax = ``Quot.sound) := by
  intro axioms
  simp [nonstandardAxioms, Array.isEmpty_iff, standardAxioms, Decidable.or_iff_not_imp_left]

ProvenTheorem assumption_names_iff : Contract Evidence.assumptionNames (fun names =>
    ∀ (e : Evidence) (n ax : Name), ax ∈ names e n ↔
      (e.ownHole = true ∧ ax = n) ∨ (e.ownHole = false ∧ ax ∈ e.assumptions)) := by
  intro e n ax
  cases h : e.ownHole <;> simp [Evidence.assumptionNames, h]

ProvenTheorem result_counts : Contract TestResults.ofResult (fun record =>
    ∀ passed, (record passed).total = 1 ∧
      (record passed).passed = if passed then 1 else 0) := by
  intro passed
  exact ⟨rfl, rfl⟩

ProvenTheorem receipt_counts : Contract TestResults.merge (fun merge =>
    ∀ (initial : TestResults) (attempts : List Bool),
    let results := attempts.foldl (fun r passed => merge r (TestResults.ofResult passed)) initial
    results.total = initial.total + attempts.length ∧
      results.passed = initial.passed + (attempts.filter id).length) := by
  intro initial attempts
  induction attempts generalizing initial with
  | nil => simp
  | cons passed attempts ih =>
    have h := ih (initial.merge (TestResults.ofResult passed))
    simp only [List.foldl_cons]
    constructor
    · rw [h.1]
      simp [TestResults.merge, TestResults.ofResult, Nat.add_assoc] <;> omega
    · rw [h.2]
      cases passed <;> simp [TestResults.merge, TestResults.ofResult, Nat.add_assoc] <;> omega

ProvenTheorem merge_preserves_bounds : ∀ (a b : TestResults),
    a.passed ≤ a.total → b.passed ≤ b.total →
      (a.merge b).passed ≤ (a.merge b).total := by
  intro a b ha hb
  simp only [TestResults.merge]
  omega

ProvenTheorem tested_iff : Contract TestResults.verdict (fun verdict =>
    ∀ r : TestResults, verdict r = some .tested ↔ 0 < r.total ∧ r.passed = r.total) := by
  intro r
  by_cases zero : r.total = 0 <;> by_cases passed : r.passed = r.total <;>
    simp [TestResults.verdict, zero, passed] <;> omega

ProvenTheorem failing_iff : ∀ r : TestResults,
    r.verdict = some .failing ↔ 0 < r.total ∧ r.passed ≠ r.total := by
  intro r
  by_cases zero : r.total = 0 <;> by_cases passed : r.passed = r.total <;>
    simp [TestResults.verdict, zero, passed] <;> omega

ProvenTheorem proof_required_iff : Contract EvidenceKind.requiresProof (fun requires =>
    ∀ kind : EvidenceKind, requires kind = true ↔ kind = .proven ∨ kind = .unitTest) := by
  intro kind
  cases kind <;> simp [EvidenceKind.requiresProof]

ProvenTheorem complete_iff : Contract Evidence.isComplete (fun complete =>
    ∀ e : Evidence, complete e = true ↔ e.kind = .proven ∨ e.kind = .unitTest ∨
      (e.kind = .derived ∧ e.assumptions = #[])) := by
  intro e
  cases e with
  | mk kind assumptions ownHole =>
    cases kind <;> simp [Evidence.isComplete, EvidenceKind.requiresProof, Array.isEmpty_iff]

ProvenTheorem evidence_labels_injective : ∀ (a b : EvidenceKind),
    toString a = toString b ↔ a = b := by
  intro a b
  cases a <;> cases b <;> simp [toString]

ProvenTheorem role_permits_iff : Contract Role.permits (fun permits =>
    ∀ source target, permits source target = true ↔ source.Allows target) := by
  intro source target
  cases source <;> cases target <;> simp [Role.permits, Role.Allows]

ProvenTheorem role_lookup : Contract Project.role? (fun lookup =>
    ∀ project name role, lookup project name = some role →
      ∃ rule ∈ project.modules, rule.name = name ∧ rule.role = role) := by
  intro project name role found
  obtain ⟨rule, found, roleEq⟩ := Option.map_eq_some_iff.mp found
  exact ⟨rule, Array.mem_of_find?_eq_some found,
    beq_iff_eq.mp (Array.find?_some (p := fun rule : ModuleRule => rule.name == name) found),
    roleEq⟩

ProvenTheorem trusted_iff : Contract Project.isTrusted (fun trusted =>
    ∀ project name, trusted project name = true ↔
      ∃ root ∈ project.trusted, root.isPrefixOf name = true) := by
  intro project name
  simp only [Project.isTrusted, Array.any_eq_true']

ProvenTheorem dependency_permits_iff : Contract Project.permits (fun permits =>
    ∀ project source target comptime,
      permits project source target comptime = true ↔
        project.Allows source target comptime) := by
  intro project source target comptime
  unfold Project.permits Project.Allows
  cases project.role? target with
  | none => exact trusted_iff project target
  | some role =>
    rw [Bool.or_eq_true]
    exact or_congr Iff.rfl (role_permits_iff source role)

ProvenTheorem declaration_check_iff : Contract DeclarationFact.check (fun check =>
    ∀ project role fact, check project role fact = true ↔
      fact.Compliant project role) := by
  intro project role fact
  have permits : ∀ target comptime,
      project.permits role target comptime = true ↔
        project.Allows role target comptime := dependency_permits_iff project role
  simp only [DeclarationFact.check, DeclarationFact.Compliant, Array.all_eq_true',
    permits, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, Array.contains_iff_mem]
  cases role <;> simp only [Bool.eq_false_iff] <;> grind

ProvenTheorem module_check_iff : Contract ModuleFact.check (fun check =>
    ∀ project fact, check project fact = true ↔ fact.Compliant project) := by
  intro project fact
  have permits : ∀ role target comptime,
      project.permits role target comptime = true ↔
        project.Allows role target comptime := dependency_permits_iff project
  unfold ModuleFact.check ModuleFact.Compliant
  cases project.role? fact.name <;>
    simp [Array.all_eq_true', -Array.all_eq_true, permits]

ProvenTheorem project_check_iff : Contract Project.check (fun check =>
    ∀ project catalog inventory,
      check project catalog inventory = true ↔ project.Compliant catalog inventory) := by
  intro project catalog inventory
  have declarationCheck : ∀ (role : Role) (fact : DeclarationFact),
      fact.check project role = true ↔ fact.Compliant project role :=
    declaration_check_iff project
  have moduleCheck : ∀ fact : ModuleFact, fact.check project = true ↔ fact.Compliant project :=
    module_check_iff project
  have owner (fact : DeclarationFact) :
      (match project.role? fact.moduleName with
        | none => false
        | some role => fact.check project role) = true ↔
      ∃ role, project.role? fact.moduleName = some role ∧ fact.Compliant project role := by
    cases project.role? fact.moduleName <;> simp [declarationCheck]
  simp only [Project.check, Project.Compliant, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.any_eq_true',
    beq_iff_eq, Array.contains_iff_mem, moduleCheck, and_assoc]
  grind

end LeanEvidence.Contracts
