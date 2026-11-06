import DeciENSSE.Bounds

/-! # Paper contract: Condition (U)

Contract entries for the section *Condition (U)* (`sec:un`): the reformulation of (U), the
runs of the source automaton, the holes and rejected paths of the unit reader, and the
decision of (U) with the closed form of its bound (`thm:un-decidable`).
-/
namespace DeciENSSE.Paper
open Core Core.Full Core.Mixed Core.Words DeciNSSE.Holes DeciNSSE.RejectedTail
variable {n : ℕ} {X Z : Type*}
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-- **Lemma (Condition (U))**, `lem:un-dead`.
Form: Absence of a live root-dead seed is written as a universally quantified implication.
-/
theorem lem_un_dead : CondU c φ ψ ↔
    ∀ x s w, DeadU c ψ (x, s) w → ¬ Live c φ (x, s, w) := condU_iff

/-- **Lemma (Runs of the source automaton)**, `lem:un-source`(1).
Form: The Boolean component is specified by its truth predicate; the state count is the cardinality of the product carrier.
-/
theorem lem_un_source_1 (p : X × Bool) (w : List (Fin n)) (j : ℕ) :
    (((targetDFA c φ ψ p).atCut w j).1 = Automata.P (signedSys c φ) p (w.take j) ∧
    (((targetDFA c φ ψ p).atCut w j).2.1 = true ↔
      (p.1, !p.2, w.take j) ∈ Mu c φ) ∧
    ((targetDFA c φ ψ p).atCut w j).2.2 =
      Automata.P (signedSys c ψ) (.inl p.1, p.2) (w.take j)) ∧
    Fintype.card (TargetState X Z) = 2 ^ (4 * Fintype.card X + 2 * Fintype.card Z + 1) := by
  refine ⟨?_, ?_⟩
  · have h := targetDFA_run (c := c) (φ := φ) (ψ := ψ) p (w.take j)
    exact ⟨h.1, h.2.1.trans mu_flip_membership.symm, h.2.2⟩
  · simp only [TargetState, Fintype.card_prod, Fintype.card_finset, Fintype.card_bool,
      Fintype.card_sum]
    ring

/-- **Lemma (Runs of the source automaton)**, `lem:un-source`(2).
-/
theorem lem_un_source_2 (p : X × Bool) (w : List (Fin n)) (j : ℕ) :
    (targetDeadT c φ ((targetDFA c φ ψ p).atCut w j) ↔ DeadT c φ p (w.take j)) ∧
    (targetDeadU c ψ ((targetDFA c φ ψ p).atCut w j) ↔ DeadU c ψ p (w.take j)) ∧
    (∀ k, j ≤ k → ¬ targetDeadT c φ ((targetDFA c φ ψ p).atCut w j) →
      ¬ targetDeadT c φ ((targetDFA c φ ψ p).atCut w k)) ∧
    (∀ k, k ≤ j → targetDeadU c ψ ((targetDFA c φ ψ p).atCut w j) →
      targetDeadU c ψ ((targetDFA c φ ψ p).atCut w k)) := by
  refine ⟨targetDFA_deadT p (w.take j), targetDFA_deadU p (w.take j), ?_, ?_⟩
  · intro k hjk hn hk
    have hp : (w.take j).IsPrefix (w.take k) := by
      simpa [List.take_take, Nat.min_eq_left hjk] using List.take_prefix j (w.take k)
    obtain ⟨z, hz⟩ := hp
    apply hn
    apply (targetDFA_deadT p (w.take j)).mpr
    apply deadT_prefix (v := z)
    rw [hz]
    exact (targetDFA_deadT p (w.take k)).mp hk
  · intro k hkj hj
    have hp : (w.take k).IsPrefix (w.take j) := by
      simpa [List.take_take, Nat.min_eq_left hkj] using List.take_prefix k (w.take j)
    obtain ⟨z, hz⟩ := hp
    apply (targetDFA_deadU p (w.take k)).mpr
    apply deadU_prefix (v := z)
    rw [hz]
    exact (targetDFA_deadU p (w.take j)).mp hj

/-- **Lemma (Runs of the source automaton)**, `lem:un-source`(3).
Form: The comparison includes its strict cut bounds explicitly.
-/
theorem lem_un_source_3 (p : X × Bool) (w : List (Fin n)) (i j : ℕ) :
    SelfEv c φ p w i j ↔ i < j ∧ j ≤ w.length ∧
      (w.drop j).IsPrefix (w.drop i) ∧
      ((targetDFA c φ ψ p).atCut w i, (targetDFA c φ ψ p).atCut w j) ∈
        targetSelfGuard (X := X) (Z := Z) := by
  rw [targetDFA_selfGuard]
  rfl

/-- **Lemma (Holes of the unit reader)**, `lem:un-holes`.
Form: Includes the consequent universal characterization of (U); signed variables index the readers.
-/
theorem lem_un_holes (hφ : ∃ ρ, SatT c ρ φ) :
    (∀ p w, IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w ↔
      Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w) ∧
    (CondU c φ ψ ↔ ∀ p w,
      ¬ IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w) :=
  ⟨fun p w => (unit_absHole_iff c φ ψ hφ p w).trans and_comm,
    condU_iff_no_unit_holes c φ ψ hφ⟩

/-- **Lemma (Rejected paths)**, `lem:un-rejected-path`.
Form: RejectedPath packages betweenness and the admission cone.
-/
theorem lem_un_rejected_path (p : X × Bool) :
    RejectedPath (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) :=
  unitRejectedPath c φ ψ p

/-- **Theorem (Condition (U) is decidable)**, `thm:un-decidable`.
Form: N_U is the cardinality of TargetState; holeLengthBound N is holeBound(N, d_N). Decidability is a computable definition for satisfiable antecedents, the executable procedure decideCondU. The closed form is stated for a nonempty visible carrier, with v = |X| and s = |X| + |Z|.
-/
def thm_un_decidable (hφ : ∃ ρ, SatT c ρ φ) :
    Decidable (CondU c φ ψ) ×'
    ((¬ CondU c φ ψ ↔ ∃ p w, w.length ≤ holeLengthBound (Fintype.card (TargetState X Z)) ∧
      Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w) ∧
    Fintype.card (TargetState X Z) = 2 ^ (4 * Fintype.card X + 2 * Fintype.card Z + 1) ∧
    (Nonempty X →
      holeLengthBound (Fintype.card (TargetState X Z)) ≤
        Bounds.E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ∧
      Bounds.E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ≤
        Bounds.E3 (20 * (Fintype.card X + Fintype.card Z) + 17))) := by
  refine ⟨decideCondU c φ ψ hφ, ?_, Bounds.card_targetState X Z,
    fun _ => Bounds.unitHoleBound_le Fintype.card_pos⟩
  rw [condU_iff_no_unit_holes c φ ψ hφ]
  push Not
  constructor
  · rintro ⟨p, w, hw⟩
    obtain ⟨v, hv, hb⟩ := (hole_iff_bounded_length (unitReader c φ ψ p)
      unitRelation (unitTarget c φ ψ)).mp ⟨w, hw⟩
    obtain ⟨hu, hl⟩ := (unit_absHole_iff c φ ψ hφ p v).mp hv
    exact ⟨p, v, hb, hl, hu⟩
  · rintro ⟨p, w, _, hl, hu⟩
    exact ⟨p, w, (unit_absHole_iff c φ ψ hφ p w).mpr ⟨hu, hl⟩⟩
end DeciENSSE.Paper
