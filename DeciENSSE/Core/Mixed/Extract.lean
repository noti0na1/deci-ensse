import DeciENSSE.Core.Mixed.Membership
import DeciENSSE.Core.Words.Self.Basic

/-! # Extracted mixed instances with negative-unit enrichment

The signed readers form two-word instances with self events. Negative units
cut off dead target prefixes, while self events detect collisions caused by a
single seed. Holes in these enriched instances are exactly the failures of the
remaining mixed entailment condition.

## Main declarations

- `extractSelf`, `extractSelf_forcedHeads`, `extractSelf_isHoleS_iff`,
  `condII_iff_no_holes`, `mixed_reduction`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Full
variable {n : ℕ}
variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Finite, executable extraction sharing the unit reader. -/
def extractSelf (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (p q : X × Bool) : SelfTwoWordInstance (Fin n) (Finset (X × Bool)) (TargetState X Z)
      (Finset ((X ⊕ Z) × Bool)) (Finset ((X ⊕ Z) × Bool)) where
  A := Automata.lower (signedSys c φ) q
  B := targetDFA c φ ψ p
  A' := Automata.lower (signedSys c ψ) (.inl q.1, q.2)
  B' := Automata.upper (signedSys c ψ) (.inl p.1, p.2)
  Bad := Finset.univ.filter fun Q => (Q ∩ PF c φ).Nonempty
  Rej := targetRej c φ ψ
  Guard := Finset.univ.filter fun S => (S.1 ∩ S.2.1).Nonempty
  Head := Finset.univ.filter fun S => (S.1 ∩ S.2).Nonempty
  SelfGuard := targetSelfGuard

variable {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
variable (p q : X × Bool)

/-- The extracted guard is an antecedent upper/lower summary intersection. -/
theorem extractSelf_guard_iff (t u : List (Fin n)) (e i : ℕ) :
    ((extractSelf c φ ψ p q).A.atCut t e, (extractSelf c φ ψ p q).B.atCut u i) ∈
      (extractSelf c φ ψ p q).Guard ↔
    (Automata.P (signedSys c φ) p (u.take i) ∩
      Automata.Q (signedSys c φ) q (t.take e)).Nonempty := by
  simp only [extractSelf, Finset.mem_filter, Finset.mem_univ, true_and,
    Automata.lower_atCut, (targetDFA_atCut p u i).1, Finset.inter_comm]

/-- Extracted rejection excludes both kinds of unit deadness. -/
theorem extractSelf_rej_iff (u : List (Fin n)) (j : ℕ) :
    (extractSelf c φ ψ p q).B.atCut u j ∈ (extractSelf c φ ψ p q).Rej ↔
      ¬ DeadT c φ p (u.take j) ∧ ¬ DeadU c ψ p (u.take j) :=
  targetDFA_rej_atCut p u j

/-- Both support languages are prefix closed, hence rejection persists. -/
theorem extractSelf_J_isSome (u : List (Fin n)) :
    ((extractSelf c φ ψ p q).J u).isSome = true ↔
      ¬ DeadT c φ p u ∧ ¬ DeadU c ψ p u := by
  constructor
  · intro h
    cases hj : (extractSelf c φ ψ p q).J u with
    | none => simp [hj] at h
    | some j =>
      obtain ⟨hr, _, _⟩ := ((extractSelf c φ ψ p q).J_eq_some_iff u j).mp hj
      obtain ⟨ht, hu⟩ := (extractSelf_rej_iff p q u j).mp hr
      constructor
      · intro hd
        exact ht (deadT_prefix (u := u.take j) (v := u.drop j) (by simpa using hd))
      · intro hd
        exact hu (deadU_prefix (u := u.take j) (v := u.drop j) (by simpa using hd))
  · intro h
    cases hj : (extractSelf c φ ψ p q).J u with
    | some j => simp
    | none =>
      have hn := ((extractSelf c φ ψ p q).J_eq_none_iff u).mp hj u.length le_rfl
      exact False.elim (hn ((extractSelf_rej_iff p q u u.length).mpr (by simpa using h)))

/-- Safety is exactly absence of positive-unit membership. -/
theorem extractSelf_safe (t : List (Fin n)) :
    (extractSelf c φ ψ p q).SafeFrom (extractSelf c φ ψ p q).A.start t ↔
      (q.1, q.2, t) ∉ Mu c φ := by
  rw [mu_membership]
  simp [TwoWordInstance.SafeFrom, extractSelf, Automata.Q, LDFA.run, Finset.mem_range,
    Nat.lt_succ_iff]

/-- Proper head prefixes are enriched support, without semantic hypotheses. -/
theorem extractSelf_forcedHeads : (extractSelf c φ ψ p q).ForcedHeads := by
  intro a b hab _ γ hγ i hi hr
  have hhead : (a ∩ b).Nonempty := by simpa [extractSelf] using hab
  have hp : (Automata.P (signedSys c ψ) (.inl p.1, p.2) γ).Nonempty := by
    change Automata.P (signedSys c ψ) (.inl p.1, p.2) γ = b at hγ
    rw [hγ]
    exact hhead.mono Finset.inter_subset_right
  exact ((extractSelf_rej_iff p q γ i).mp hr).2 (head_prefix_deadU hp hi)

/-- Nonempty antecedent upper cuts precede every enriched first rejection. -/
theorem extractSelf_cut_le_J {u : List (Fin n)} {i j : ℕ}
    (hj : (extractSelf c φ ψ p q).J u = some j) (hi : i ≤ u.length)
    (hp : (Automata.P (signedSys c φ) p (u.take i)).Nonempty) : i ≤ j := by
  have ht := ((extractSelf_rej_iff p q u j).mp
    (((extractSelf c φ ψ p q).J_eq_some_iff u j).mp hj).1).1
  by_contra hn
  have he := cone ht (by omega : j < i) hi
  simp [he] at hp

/-- Pointwise cross events. Defined enriched J is essential here. -/
theorem extractSelf_event_at_iff {t u : List (Fin n)}
    (hJ : ((extractSelf c φ ψ p q).J u).isSome = true) (e i : ℕ) :
    (extractSelf c φ ψ p q).Event t u e i ↔
      i ≤ u.length ∧ e ≤ t.length ∧ (u.drop i).IsPrefix (t.drop e) ∧
      (Automata.P (signedSys c φ) p (u.take i) ∩
        Automata.Q (signedSys c φ) q (t.take e)).Nonempty := by
  constructor
  · rintro ⟨⟨he, hi, hpre⟩, _, hg⟩
    exact ⟨hi, he, hpre, (extractSelf_guard_iff p q t u e i).mp hg⟩
  · rintro ⟨hi, he, hpre, hg⟩
    refine ⟨⟨he, hi, hpre⟩, ?_, (extractSelf_guard_iff p q t u e i).mpr hg⟩
    cases hj : (extractSelf c φ ψ p q).J u with
    | none => simp [hj] at hJ
    | some j => exact ⟨j, rfl, extractSelf_cut_le_J p q hj hi
        (hg.mono Finset.inter_subset_left)⟩

/-- Extracted comparison events are exactly the cut-based antecedent events. -/
theorem extractSelf_event_iff {t u : List (Fin n)}
    (hJ : ((extractSelf c φ ψ p q).J u).isSome = true) :
    (∃ e i, (extractSelf c φ ψ p q).Event t u e i) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.P (signedSys c φ) p (u.take i) ∩
          Automata.Q (signedSys c φ) q (t.take e)).Nonempty := by
  simp only [extractSelf_event_at_iff p q hJ]
  constructor
  · rintro ⟨e, i, hi, he, hpre, hg⟩; exact ⟨i, hi, e, he, hpre, hg⟩
  · rintro ⟨i, hi, e, he, hpre, hg⟩; exact ⟨e, i, hi, he, hpre, hg⟩

/-- Pointwise self events, using the second upper cut for the cone bound. -/
theorem extractSelf_selfEvent_at_iff {u : List (Fin n)}
    (hJ : ((extractSelf c φ ψ p q).J u).isSome = true) (i j : ℕ) :
    (extractSelf c φ ψ p q).SelfEvent u i j ↔ SelfEv c φ p u i j := by
  have hg := targetDFA_selfGuard (c := c) (φ := φ) (ψ := ψ) p u i j
  constructor
  · rintro ⟨hij, ⟨_, hj, hpre⟩, _, hguard⟩
    exact ⟨hij, hj, hpre, hg.mp hguard⟩
  · rintro ⟨hij, hj, hpre, hguard⟩
    refine ⟨hij, ⟨by omega, hj, hpre⟩, ?_, hg.mpr hguard⟩
    have hp := (flip_inter_symm.mp hguard).mono Finset.inter_subset_left
    cases hk : (extractSelf c φ ψ p q).J u with
    | none => simp [hk] at hJ
    | some k => exact ⟨k, rfl, extractSelf_cut_le_J p q hk hj hp⟩

/-- A consequent path supplies an extracted head event. -/
theorem extractSelf_head (t u : List (Fin n)) :
    (extractSelf c φ ψ p q).HasHeadEvent t u ↔
      Moves c ψ (.inl p.1, p.2, u) (.inl q.1, q.2, t) := by
  change _ ↔ Relation.ReflTransGen (Move c ψ) _ _
  rw [lowest_point_leaf]
  simp only [TwoWordInstance.HasHeadEvent, TwoWordInstance.HeadEvent, TwoWordInstance.Aligned,
    extractSelf,
    Automata.upper_atCut, Automata.lower_atCut, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_range, Nat.lt_succ_iff, Finset.inter_comm]
  constructor
  · rintro ⟨e, he, i, hi, ⟨_, _, h⟩, hg⟩
    exact ⟨i, hi, e, he, h.symm, hg⟩
  · rintro ⟨i, hi, e, he, h, hg⟩
    exact ⟨e, he, i, hi, ⟨he, hi, h.symm⟩, hg⟩

/-- Failure of antecedent closure excludes all extracted comparison events. -/
theorem extractSelf_no_events {t u : List (Fin n)}
    (hJ : ((extractSelf c φ ψ p q).J u).isSome = true) :
    (∀ e ∈ Finset.range (t.length + 1), ∀ i ∈ Finset.range (u.length + 1),
      ¬ (extractSelf c φ ψ p q).Event t u e i) ↔
    ¬ ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
      (Automata.P (signedSys c φ) p (u.take i) ∩
        Automata.Q (signedSys c φ) q (t.take e)).Nonempty := by
  rw [← extractSelf_event_iff p q hJ]
  constructor
  · intro h ⟨e, i, he⟩
    exact h e (Finset.mem_range.mpr (by have := he.1.1; omega))
      i (Finset.mem_range.mpr (by have := he.1.2.1; omega)) he
  · intro h e _ i _ he; exact h ⟨e, i, he⟩

/-- Liveness excludes extracted self events. -/
theorem extractSelf_noSelf {u : List (Fin n)}
    (hJ : ((extractSelf c φ ψ p q).J u).isSome = true) :
    (extractSelf c φ ψ p q).NoSelf u ↔ ¬ ∃ i j, SelfEv c φ p u i j := by
  rw [SelfTwoWordInstance.noSelf_iff]
  simp only [extractSelf_selfEvent_at_iff p q hJ, not_exists]

/-- Holes are exactly the live pure-path failures of closure, under (U). -/
theorem extractSelf_isHoleS_iff (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    (t u : List (Fin n)) :
    (extractSelf c φ ψ p q).IsHole t u ↔
      Live c φ (p.1, p.2, u) ∧
      Moves c ψ (.inl p.1, p.2, u) (.inl q.1, q.2, t) ∧
      (q.1, q.2, t) ∉ Cl c φ (p.1, p.2, u) := by
  classical
  have hlive := dead_iff_unit_or_self (sat_iff_mu.mp hφ) (p := p) (u := u)
  constructor
  · rintro ⟨⟨hs, hj, he, hh⟩, hn⟩
    have ht := ((extractSelf_J_isSome p q u).mp hj).1
    have hns := (extractSelf_noSelf p q hj).mp hn
    have hl : Live c φ (p.1, p.2, u) := by
      by_contra hn
      exact (hlive.mp hn).elim ht hns
    refine ⟨hl, (extractSelf_head p q t u).mp hh, ?_⟩
    rw [cl_membership_live hl]
    exact not_or.mpr ⟨(extractSelf_safe p q t).mp hs, (extractSelf_no_events p q hj).mp he⟩
  · rintro ⟨hl, hh, hc⟩
    have ht : ¬ DeadT c φ p u := fun h => deadT_not_live h hl
    have hu : ¬ DeadU c ψ p u := fun h => (condU_iff.mp hU) p.1 p.2 u h hl
    have hj := (extractSelf_J_isSome p q u).mpr ⟨ht, hu⟩
    have hcl := not_or.mp (mt (cl_membership_live hl).mpr hc)
    refine ⟨⟨(extractSelf_safe p q t).mpr hcl.1, hj,
      (extractSelf_no_events p q hj).mpr hcl.2, (extractSelf_head p q t u).mpr hh⟩,
      (extractSelf_noSelf p q hj).mpr ?_⟩
    intro hs
    exact (hlive.mpr (Or.inr hs)) hl

/-- The extracted interface for the finite decision procedure. -/
theorem condII_iff_no_holes (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ) :
    CondII c φ ψ ↔ ∀ p q, ¬ (extractSelf c φ ψ p q).HasHole := by
  rw [condII_iff_moves]
  constructor
  · intro h p q ⟨t, u, hh⟩
    obtain ⟨hl, hm, hn⟩ := (extractSelf_isHoleS_iff p q hφ hU t u).mp hh
    exact hn (h (p.1, p.2, u) (q.1, q.2, t) hl hm)
  · intro h ⟨p, s, u⟩ ⟨q, s', t⟩ hl hm
    by_contra hn
    exact h (p, s) (q, s') ⟨t, u, (extractSelf_isHoleS_iff _ _ hφ hU t u).mpr ⟨hl, hm, hn⟩⟩

/-- Satisfiability-dispatched reduction, with (U) tested before holes. -/
theorem mixed_reduction (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧
      ∀ p q, ¬ (extractSelf c φ ψ p q).HasHole := by
  rw [three_conditions_mixed hφ hψ]
  constructor
  · rintro ⟨hi, hu, hii⟩; exact ⟨hi, hu, (condII_iff_no_holes hφ hu).mp hii⟩
  · rintro ⟨hi, hu, hh⟩; exact ⟨hi, hu, (condII_iff_no_holes hφ hu).mpr hh⟩

end DeciENSSE.Core.Mixed
