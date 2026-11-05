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
      simp [TestResults.merge, TestResults.ofResult, Nat.add_assoc]
      omega
    · rw [h.2]
      cases passed with
      | false => simp [TestResults.merge, TestResults.ofResult]
      | true =>
        simp [TestResults.merge, TestResults.ofResult, Nat.add_assoc]
        omega

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
    simp [TestResults.verdict, zero, passed, Nat.pos_iff_ne_zero]

ProvenTheorem failing_iff : ∀ r : TestResults,
    r.verdict = some .failing ↔ 0 < r.total ∧ r.passed ≠ r.total := by
  intro r
  by_cases zero : r.total = 0 <;> by_cases passed : r.passed = r.total <;>
    simp [TestResults.verdict, zero, passed, Nat.pos_iff_ne_zero]

ProvenTheorem requirement_complete_iff : Contract (@Requirement.isComplete) (fun complete =>
    ∀ (statement : Prop) (r : Requirement statement),
      complete r = true ↔ ∃ witness, r.witness = some witness) := by
  intro statement r
  simp [Requirement.isComplete, Option.isSome_iff_exists]

ProvenTheorem requirement_complete_sound : ∀ (statement : Prop) (r : Requirement statement),
    r.isComplete = true → statement := by
  intro statement r complete
  obtain ⟨witness, _⟩ := (requirement_complete_iff statement r).mp complete
  exact witness.down

ProvenTheorem claim_complete_iff : Contract ClaimFact.isComplete (fun complete =>
    ∀ claim, complete claim = true ↔ claim.verified = true ∧
      ∃ evidence, claim.evidence = some evidence) := by
  intro claim
  simp [ClaimFact.isComplete, Option.isSome_iff_exists]

ProvenTheorem claims_complete_iff : Contract Claims.isComplete (fun complete =>
    ∀ inventories claims, complete inventories claims = true ↔ Claims.Complete inventories claims) := by
  intro inventories claims
  simp only [Claims.isComplete, Claims.Complete, Bool.and_eq_true, Bool.not_eq_true',
    Array.isEmpty_eq_false_iff, decide_eq_true_eq, Array.all_eq_true', Array.any_eq_true',
    beq_iff_eq, Array.contains_iff_mem, ClaimFact.isComplete, Bool.and_eq_true,
    Option.isSome_iff_exists]
  grind

ProvenTheorem outstanding_iff : Contract Claims.outstanding (fun pending =>
    ∀ claims name, name ∈ pending claims ↔ ∃ claim ∈ claims,
      claim.name = name ∧ (claim.verified = false ∨ claim.evidence = none)) := by
  intro claims name
  simp [Claims.outstanding, ClaimFact.isComplete, Array.mem_filter]
  grind

ProvenTheorem complete_has_no_outstanding : ∀ inventories claims,
    Claims.isComplete inventories claims = true → Claims.outstanding claims = #[] := by
  intro inventories claims complete
  have satisfied := ((claims_complete_iff inventories claims).mp complete).2.2.2.2
  apply Array.eq_empty_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨claim, member, _, incomplete⟩ := (outstanding_iff claims name).mp member
  obtain ⟨_, verified, evidence, present⟩ := satisfied claim member
  simp_all

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

ProvenTheorem project_complete_iff : Contract Project.isComplete (fun complete =>
    ∀ project catalog inventory, complete project catalog inventory = true ↔
      project.Compliant catalog inventory ∧
        Claims.Complete project.requirements inventory.claims) := by
  intro project catalog inventory
  rw [Project.isComplete, Bool.and_eq_true]
  exact and_congr (project_check_iff project catalog inventory)
    (claims_complete_iff project.requirements inventory.claims)

Requirements obligations where
  proof standard_axioms : Contract nonstandardAxioms (fun classify =>
    ∀ axioms : Array Name, (classify axioms).isEmpty = true ↔
      ∀ ax ∈ axioms, ax = ``propext ∨ ax = ``Classical.choice ∨ ax = ``Quot.sound) :=
    standard_axioms_iff
  proof assumption_names : Contract Evidence.assumptionNames (fun names =>
    ∀ (e : Evidence) (n ax : Name), ax ∈ names e n ↔
      (e.ownHole = true ∧ ax = n) ∨ (e.ownHole = false ∧ ax ∈ e.assumptions)) :=
    assumption_names_iff
  proof result_counts : Contract TestResults.ofResult (fun record =>
    ∀ passed, (record passed).total = 1 ∧
      (record passed).passed = if passed then 1 else 0) := result_counts
  proof receipt_counts : Contract TestResults.merge (fun merge =>
    ∀ (initial : TestResults) (attempts : List Bool),
    let results := attempts.foldl (fun r passed => merge r (TestResults.ofResult passed)) initial
    results.total = initial.total + attempts.length ∧
      results.passed = initial.passed + (attempts.filter id).length) := receipt_counts
  proof merge_bounds : ∀ (a b : TestResults),
    a.passed ≤ a.total → b.passed ≤ b.total →
      (a.merge b).passed ≤ (a.merge b).total := merge_preserves_bounds
  proof tested : Contract TestResults.verdict (fun verdict =>
    ∀ r : TestResults, verdict r = some .tested ↔ 0 < r.total ∧ r.passed = r.total) :=
    tested_iff
  proof failing : ∀ r : TestResults,
    r.verdict = some .failing ↔ 0 < r.total ∧ r.passed ≠ r.total := failing_iff
  proof requirement_completion : Contract (@Requirement.isComplete) (fun complete =>
    ∀ (statement : Prop) (r : Requirement statement),
      complete r = true ↔ ∃ witness, r.witness = some witness) := requirement_complete_iff
  proof requirement_soundness : ∀ (statement : Prop) (r : Requirement statement),
    r.isComplete = true → statement := requirement_complete_sound
  proof claim_completion : Contract ClaimFact.isComplete (fun complete =>
    ∀ claim, complete claim = true ↔ claim.verified = true ∧
      ∃ evidence, claim.evidence = some evidence) := claim_complete_iff
  proof inventory_completion : Contract Claims.isComplete (fun complete =>
    ∀ inventories claims, complete inventories claims = true ↔
      Claims.Complete inventories claims) := claims_complete_iff
  proof outstanding : Contract Claims.outstanding (fun pending =>
    ∀ claims name, name ∈ pending claims ↔ ∃ claim ∈ claims,
      claim.name = name ∧ (claim.verified = false ∨ claim.evidence = none)) := outstanding_iff
  proof no_outstanding : ∀ inventories claims,
    Claims.isComplete inventories claims = true → Claims.outstanding claims = #[] :=
    complete_has_no_outstanding
  proof proof_required : Contract EvidenceKind.requiresProof (fun requires =>
    ∀ kind : EvidenceKind, requires kind = true ↔ kind = .proven ∨ kind = .unitTest) :=
    proof_required_iff
  proof evidence_completion : Contract Evidence.isComplete (fun complete =>
    ∀ e : Evidence, complete e = true ↔ e.kind = .proven ∨ e.kind = .unitTest ∨
      (e.kind = .derived ∧ e.assumptions = #[])) := complete_iff
  proof evidence_labels : ∀ (a b : EvidenceKind), toString a = toString b ↔ a = b :=
    evidence_labels_injective
  proof role_permissions : Contract Role.permits (fun permits =>
    ∀ source target, permits source target = true ↔ source.Allows target) := role_permits_iff
  proof role_lookup : Contract Project.role? (fun lookup =>
    ∀ project name role, lookup project name = some role →
      ∃ rule ∈ project.modules, rule.name = name ∧ rule.role = role) := role_lookup
  proof trusted_modules : Contract Project.isTrusted (fun trusted =>
    ∀ project name, trusted project name = true ↔
      ∃ root ∈ project.trusted, root.isPrefixOf name = true) := trusted_iff
  proof dependency_permissions : Contract Project.permits (fun permits =>
    ∀ project source target comptime, permits project source target comptime = true ↔
      project.Allows source target comptime) := dependency_permits_iff
  proof declarations : Contract DeclarationFact.check (fun check =>
    ∀ project role fact, check project role fact = true ↔ fact.Compliant project role) :=
    declaration_check_iff
  proof modules : Contract ModuleFact.check (fun check =>
    ∀ project fact, check project fact = true ↔ fact.Compliant project) := module_check_iff
  proof project_policy : Contract Project.check (fun check =>
    ∀ project catalog inventory,
      check project catalog inventory = true ↔ project.Compliant catalog inventory) :=
    project_check_iff
  proof project_completion : Contract Project.isComplete (fun complete =>
    ∀ project catalog inventory, complete project catalog inventory = true ↔
      project.Compliant catalog inventory ∧
        Claims.Complete project.requirements inventory.claims) := project_complete_iff

end LeanEvidence.Contracts
