import DeciENSSE.Core.Automata
import DeciENSSE.Core.Words.Transport

/-! # Extracted suffix-sharing instances

Upper and lower automata extract suffix-sharing instances. Their holes capture
failures of the third Horn condition and supply countermodels.

## Main declarations

- `extract`
- `extract_fh`
- `extract_isHole_iff`
- `condIII_iff_no_holes`
- `ss2_reduction`
- `hole_countermodel`
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Bound
variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- The suffix-sharing instance extracted from two visible variables. -/
def extract (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) (x y : X) :
    SS2 (Fin n) (Finset X) (Finset X) (Finset (X ⊕ Z)) (Finset (X ⊕ Z)) where
  A := upper φ x
  B := lower φ y
  A' := upper ψ (.inl x)
  B' := lower ψ (.inl y)
  Bad := badStates φ
  Rej := rejectedStates φ
  Guard := overlapStates X
  Head := overlapStates (X ⊕ Z)

variable {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}

/-- The extracted instance has the same first rejection index. -/
@[simp] theorem extract_J (x y : X) (t : List (Fin n)) :
    (extract φ ψ x y).J t = Bound.J φ y t := by
  simp [SS2.J, Bound.J, extract]

/-- Safety of the extracted instance agrees with upper-automaton safety. -/
@[simp] theorem extract_safe (x y : X) (u : List (Fin n)) :
    (extract φ ψ x y).SafeFrom (extract φ ψ x y).A.start u ↔ Safe φ x u := by
  simp [SS2.SafeFrom, extract, Safe, P, LDFA.run]

/-- A head event in the extracted instance witnesses consequent reachability. -/
@[simp] theorem extract_head (x y : X) (u t : List (Fin n)) :
    (extract φ ψ x y).HasHeadEvent u t ↔
      Moves ψ (.inl x, u) (.inl y, t) := by
  rw [lowest_point]
  simp only [SS2.HasHeadEvent, SS2.HeadEvent, SS2.Aligned, extract,
    upper_atCut, lower_atCut, mem_overlapStates, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨s, hs, e, he, ⟨_, _, hst⟩, hm⟩
    exact ⟨s, hs, e, he, hst, hm⟩
  · rintro ⟨s, hs, e, he, hst, hm⟩
    exact ⟨s, hs, e, he, ⟨hs, he, hst⟩, hm⟩

/-- A defined first rejection is exactly absence from the least solution. -/
theorem extract_rejected (x y : X) (t : List (Fin n)) :
    ((extract φ ψ x y).J t).isSome = true ↔ (y, t) ∉ Mu φ := by
  rw [extract_J]
  constructor
  · intro hj hm
    cases hJ : Bound.J φ y t with
    | none => simp [hJ] at hj
    | some j =>
      have hd := ((Bound.J_eq_some_iff φ y t j).mp hJ).1
      have hp := Q_fact_prefix (List.take_prefix j t) (mu_membership.mp hm)
      exact (Finset.not_disjoint_iff_nonempty_inter.mpr hp) hd
  · intro hm
    have hd : Disjoint (Q φ y t) (LowF φ) := by
      simpa only [← Finset.not_disjoint_iff_nonempty_inter, not_not] using
        (mt mu_membership.mpr hm)
    obtain ⟨j, hj⟩ := J_defined hd
    simp [hj]

/-- Under first rejection, every possible closure overlap is an SS2 event. -/
theorem extract_no_events (x y : X) (u t : List (Fin n))
    (hj : ((extract φ ψ x y).J t).isSome = true) :
    (∀ s ∈ Finset.range (u.length + 1), ∀ e ∈ Finset.range (t.length + 1),
      ¬ (extract φ ψ x y).Event u t s e) ↔
    ¬ ∃ s ≤ u.length, ∃ e ≤ t.length,
      (P φ x (u.take s) ∩ Q φ y (t.take e)).Nonempty ∧
      (t.drop e).IsPrefix (u.drop s) := by
  cases hJ : Bound.J φ y t with
  | none => simp [extract_J, hJ] at hj
  | some j =>
    constructor
    · intro hn ⟨s, hs, e, he, hm, hp⟩
      apply hn s (Finset.mem_range.mpr (by omega)) e (Finset.mem_range.mpr (by omega))
      refine ⟨⟨hs, he, hp⟩, ?_, ?_⟩
      · exact ⟨j, by simpa using hJ, cl_cuts_before_J hJ he hm⟩
      · simpa [extract] using hm
    · intro hn s hs e he hv
      exact hn ⟨s, Nat.le_of_lt_succ (Finset.mem_range.mp hs), e,
        Nat.le_of_lt_succ (Finset.mem_range.mp he), by simpa [extract] using hv.2.2,
        hv.1.2.2⟩

/-- Extracted holes correspond to individual failures of visible closure. -/
theorem extract_isHole_iff (hφ : ∃ ρ, Sat ρ φ) (x y : X) (u t : List (Fin n)) :
    (extract φ ψ x y).IsHole u t ↔
      (x, u) ∈ Live φ ∧ Moves ψ (.inl x, u) (.inl y, t) ∧
        (y, t) ∉ Cl φ (x, u) := by
  constructor
  · rintro ⟨hs, hj, hn, hh⟩
    refine ⟨(liveness hφ x u).mpr ((extract_safe x y u).mp hs),
      (extract_head x y u t).mp hh, ?_⟩
    intro hc
    rcases cl_membership.mp hc with hm | hc
    · exact (extract_rejected x y t).mp hj (mu_membership.mpr hm)
    · exact (extract_no_events x y u t hj).mp hn hc
  · rintro ⟨hl, hm, hc⟩
    have hmu : (y, t) ∉ Mu φ := fun h => hc (Or.inl h)
    have hj := (extract_rejected (ψ := ψ) x y t).mpr hmu
    refine ⟨(extract_safe x y u).mpr ((liveness hφ x u).mp hl), hj,
      (extract_no_events x y u t hj).mpr ?_, (extract_head x y u t).mpr hm⟩
    exact fun h => hc (cl_membership.mpr (Or.inr h))

/-- The first Horn condition supplies the extracted head-closure property. -/
theorem extract_fh (hi : CondI φ ψ) (x y : X) : (extract φ ψ x y).FH := by
  intro p q hp _ γ hγ i hiγ
  have hn : (Q ψ (.inl y) γ).Nonempty := by
    have hm : (p ∩ q).Nonempty := by simpa [extract] using hp
    rw [show Q ψ (.inl y) γ = q from hγ]
    exact hm.mono Finset.inter_subset_right
  have hψ : (.inl y, γ.take i) ∈ Mu ψ := mu_membership.mpr
    (Finset.not_disjoint_iff_nonempty_inter.mp (cone_prefix hn hiγ))
  have hφ := mu_membership.mp (hi (a := (y, γ.take i)) hψ)
  simpa [extract, ← Finset.not_disjoint_iff_nonempty_inter] using hφ

/-- The third Horn condition excludes all extracted holes. Full reachability is handled by
postponing truncations and using prefix closure of the antecedent closure. -/
theorem condIII_iff_no_holes (hφ : ∃ ρ, Sat ρ φ) :
    CondIII φ ψ ↔ ∀ x y, ¬ (extract φ ψ x y).HasHole := by
  classical
  constructor
  · intro h x y ⟨u, t, hh⟩
    obtain ⟨hl, hm, hc⟩ := (extract_isHole_iff hφ x y u t).mp hh
    exact hc (h (x, u) hl hm.reach)
  · intro h ⟨x, u⟩ hl ⟨y, t⟩ hr
    change Reach ψ (.inl x, u) (.inl y, t) at hr
    obtain ⟨W, hm, v, hv⟩ := truncation.mp hr
    have hc : (y, W) ∈ Cl φ (x, u) := by
      by_contra hn
      exact h x y ⟨u, W, (extract_isHole_iff hφ x y u W).mpr ⟨hl, hm, hn⟩⟩
    exact (cl_closed (x, u)).prefixClosed y t v (by simpa [hv] using hc)

/-- Failure of the third Horn condition gives an extracted hole. -/
theorem not_condIII_iff_hole (hφ : ∃ ρ, Sat ρ φ) :
    ¬ CondIII φ ψ ↔ ∃ x y, (extract φ ψ x y).HasHole := by
  classical
  simp only [condIII_iff_no_holes hφ, not_forall, not_not]

/-- Entailment is equivalent to the first two conditions and absence of extracted holes. -/
theorem ss2_reduction (hφ : ∃ ρ, Sat ρ φ) (hψ : ∃ ρ, Sat ρ ψ) :
    ExistsEntails φ ψ ↔ CondI φ ψ ∧ CondII φ ψ ∧
      ∀ x y, ¬ (extract φ ψ x y).HasHole := by
  rw [three_conditions hφ hψ, condIII_iff_no_holes hφ]

/-- The least solution containing the seed is a countermodel, stated in the Horn representation of
assignments. -/
theorem hole_countermodel (hφ : ∃ ρ, Sat ρ φ) {x y : X} {u t : List (Fin n)}
    (hh : (extract φ ψ x y).IsHole u t) :
    Sol φ (Cl φ (x, u)) ∧ Cl φ (x, u) ∉ Projected ψ := by
  obtain ⟨hl, hm, hc⟩ := (extract_isHole_iff hφ x y u t).mp hh
  refine ⟨cl_sol hl, ?_⟩
  rintro ⟨T, hT, hres⟩
  have ha : visible (x, u) ∈ T := by
    change (x, u) ∈ restrict T
    rw [hres]; exact mem_cl _
  have hb := hm.reach.mem_of_closed hT.closed ha
  apply hc
  rw [← hres]
  exact hb

end DeciENSSE.Core
