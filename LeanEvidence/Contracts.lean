module

public meta import LeanEvidence.Commands
import all LeanEvidence.Evidence

public section
meta section

open Lean

namespace LeanEvidence.Contracts

ProvenTheorem standard_axioms_iff : ∀ axioms : Array Name,
    (nonstandardAxioms axioms).isEmpty = true ↔
      ∀ ax ∈ axioms, ax = ``propext ∨ ax = ``Classical.choice ∨ ax = ``Quot.sound := by
  intro axioms
  simp [nonstandardAxioms, Array.isEmpty_iff, standardAxioms, Decidable.or_iff_not_imp_left]

ProvenTheorem assumption_names_iff : ∀ (e : Evidence) (n ax : Name),
    ax ∈ e.assumptionNames n ↔
      (e.ownHole = true ∧ ax = n) ∨ (e.ownHole = false ∧ ax ∈ e.assumptions) := by
  intro e n ax
  cases h : e.ownHole <;> simp [Evidence.assumptionNames, h]

ProvenTheorem receipt_counts : ∀ (initial : TestResults) (attempts : List Bool),
    let results := attempts.foldl (fun r passed => r.merge (TestResults.ofResult passed)) initial
    results.total = initial.total + attempts.length ∧
      results.passed = initial.passed + (attempts.filter id).length := by
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

ProvenTheorem tested_iff : ∀ r : TestResults,
    r.verdict = some .tested ↔ 0 < r.total ∧ r.passed = r.total := by
  intro r
  by_cases zero : r.total = 0 <;> by_cases passed : r.passed = r.total <;>
    simp [TestResults.verdict, zero, passed] <;> omega

ProvenTheorem failing_iff : ∀ r : TestResults,
    r.verdict = some .failing ↔ 0 < r.total ∧ r.passed ≠ r.total := by
  intro r
  by_cases zero : r.total = 0 <;> by_cases passed : r.passed = r.total <;>
    simp [TestResults.verdict, zero, passed] <;> omega

ProvenTheorem proof_required_iff : ∀ kind : EvidenceKind,
    kind.requiresProof = true ↔ kind = .proven ∨ kind = .unitTest := by
  intro kind
  cases kind <;> simp [EvidenceKind.requiresProof]

ProvenTheorem complete_iff : ∀ e : Evidence,
    e.isComplete = true ↔ e.kind = .proven ∨ e.kind = .unitTest ∨
      (e.kind = .derived ∧ e.assumptions = #[]) := by
  intro e
  cases e with
  | mk kind assumptions ownHole =>
    cases kind <;> simp [Evidence.isComplete, EvidenceKind.requiresProof, Array.isEmpty_iff]

ProvenTheorem evidence_labels_injective : ∀ (a b : EvidenceKind),
    toString a = toString b ↔ a = b := by
  intro a b
  cases a <;> cases b <;> simp [toString]

end LeanEvidence.Contracts
