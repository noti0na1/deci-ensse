import DeciENSSE.Core.Full.ACPins
import DeciENSSE.Core.Full.Classes
import DeciENSSE.Core.Mixed.LeafHorn

/-! # Transferring entailment through observations

A failed extension is retained by at most two observations of visible leaf
atoms. Realizing these observations in a tree class and keeping visible values
fixed when choosing hidden witnesses transfers entailment to that class.
Ground bounds encode the observations as finite comparisons for pinning.

## Main declarations

- `two_observations_mixed`: at most two observations retain a failed extension
  (`lem:tc-two-seeds`).
- `existsEntailsTIn_iff_of_transfer`: transfer to a class with both obligations.
- `fin_dispatch_of_transfer`: account for finite satisfiability of both systems.
- `BoundRealization.observations`: ground bounds supply observation realization.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

/-- A signed leaf atom, asserted or denied. -/
abbrev Observation (n : ℕ) (V : Type*) := Config n V × Bool

/-- Interpret the observation on a tree assignment. -/
def Observation.Holds {V : Type*} (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n)
    (o : Observation n V) : Prop :=
  if o.2 then o.1 ∈ configSet c ρ else o.1 ∉ configSet c ρ

/-- A derived atom has either fact ancestry or one visible seed ancestor. -/
private theorem hull_ancestor {X Z : Type*} {c : Fin n → Bool}
    {ψ : List (LitT n (X ⊕ Z))} {ρ : X → DeciNSSE.Tree n} {b : Config n (X ⊕ Z)}
    (hb : b ∈ Hull c ψ (visibleSeeds c ρ)) :
    (∀ τ, SatT c τ ψ → b ∈ configSet c τ) ∨
    ∃ a : Observation n X, a.Holds c ρ ∧ ∀ ρ' σ,
      a.Holds c ρ' → SatT c (Sum.elim ρ' σ) ψ →
      b ∈ configSet c (Sum.elim ρ' σ) := by
  obtain ⟨f, hf | ⟨a, ha, rfl⟩, hr⟩ := hb
  · exact Or.inl fun τ ht => hr.mem_of_closed ((sat_iff_sol τ).mp ht).closed
      (((sat_iff_sol τ).mp ht).facts hf)
  · exact Or.inr ⟨(a, true), ha, fun ρ' σ hp ht =>
      hr.mem_of_closed ((sat_iff_sol _).mp ht).closed hp⟩

/-- **Two seeds** (`lem:tc-two-seeds`). Failure of extension is retained by at
most two observations that hold in `ρ`: no assignment satisfying them is
extensible. There is no satisfiability hypothesis on `ψ`; an obstruction
supported by facts alone (`ψ` unsatisfiable) is retained by no observation. -/
theorem two_observations_mixed {X Z : Type*} {c : Fin n → Bool}
    {ψ : List (LitT n (X ⊕ Z))}
    (ρ : X → DeciNSSE.Tree n) (hne : ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) :
    ∃ O : List (Observation n X), O.length ≤ 2 ∧ (∀ o ∈ O, o.Holds c ρ) ∧
      ∀ ρ', (∀ o ∈ O, o.Holds c ρ') → ¬ ∃ σ, SatT c (Sum.elim ρ' σ) ψ := by
  classical
  by_cases hn : Avoids ψ (Hull c ψ (visibleSeeds c ρ))
  · by_cases hc : Consistent (Hull c ψ (visibleSeeds c ρ))
    · have hv : ¬ restrict (Hull c ψ (visibleSeeds c ρ)) ⊆ configSet c ρ :=
        fun hv => hne ((extends_iff_hull ρ ψ).mpr ⟨hn, hc, hv⟩)
      obtain ⟨b, hb, hnb⟩ := Set.not_subset.mp hv
      have hnb' : Observation.Holds c ρ (b, false) := hnb
      rcases hull_ancestor hb with hf | ⟨a, ha, hp⟩
      · refine ⟨[(b, false)], by simp, List.forall_mem_singleton.mpr hnb', ?_⟩
        rintro ρ' hO ⟨σ, hs⟩
        exact (hO (b, false) (by simp) : Observation.Holds c ρ' (b, false)) (hf _ hs)
      · refine ⟨[a, (b, false)], by simp,
          List.forall_mem_cons.mpr ⟨ha, List.forall_mem_singleton.mpr hnb'⟩, ?_⟩
        rintro ρ' hO ⟨σ, hs⟩
        exact (hO (b, false) (by simp) : Observation.Holds c ρ' (b, false))
          (hp ρ' σ (hO a (by simp)) hs)
    · simp only [Consistent] at hc
      push Not at hc
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hc
      rcases hull_ancestor hp with hf | ⟨a, ha, hpa⟩ <;>
        rcases hull_ancestor hq with hg | ⟨b, hb, hpb⟩
      · refine ⟨[], by simp, by simp, ?_⟩
        rintro ρ' - ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq (hf _ hs) (hg _ hs)
      · refine ⟨[b], by simp, List.forall_mem_singleton.mpr hb, ?_⟩
        rintro ρ' hO ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq (hf _ hs)
          (hpb ρ' σ (hO b (by simp)) hs)
      · refine ⟨[a], by simp, List.forall_mem_singleton.mpr ha, ?_⟩
        rintro ρ' hO ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq (hpa ρ' σ (hO a (by simp)) hs)
          (hg _ hs)
      · refine ⟨[a, b], by simp,
          List.forall_mem_cons.mpr ⟨ha, List.forall_mem_singleton.mpr hb⟩, ?_⟩
        rintro ρ' hO ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq
          (hpa ρ' σ (hO a (by simp)) hs) (hpb ρ' σ (hO b (by simp)) hs)
  · simp only [Avoids, not_forall, not_not] at hn
    obtain ⟨p, hp, hneg⟩ := hn
    rcases hull_ancestor hp with hf | ⟨a, ha, hpa⟩
    · refine ⟨[], by simp, by simp, ?_⟩
      rintro ρ' - ⟨σ, hs⟩
      exact ((sat_iff_sol _).mp hs).avoids (hf _ hs) hneg
    · refine ⟨[a], by simp, List.forall_mem_singleton.mpr ha, ?_⟩
      rintro ρ' hO ⟨σ, hs⟩
      exact ((sat_iff_sol _).mp hs).avoids (hpa ρ' σ (hO a (by simp)) hs) hneg

/-- Covariant observation on the positively normalized tree. -/
def Observation.normalized {V : Type*} (o : Observation n V) : Full.Observation n V :=
  ⟨!o.1.2.1, o.1.1, o.1.2.2, !o.2⟩

/-- Normalizing a mixed observation gives the equivalent covariant observation. -/
theorem observation_normalized {V : Type*} (c : Fin n → Bool)
    (ρ : V → DeciNSSE.Tree n) (o : Observation n V) :
    o.normalized.Holds (fun v => DeciNSSE.Tree.normalize c false (ρ v)) ↔ o.Holds c ρ := by
  obtain ⟨⟨v, s, w⟩, b⟩ := o
  cases s <;> cases b <;>
    simp only [Observation.normalized, Full.Observation.Holds, Observation.Holds,
      configSet, Set.mem_ofPred_eq, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true]
  · simpa only [leaf, Set.mem_ofPred_eq] using
      AC.cobs_dual (DeciNSSE.Tree.normalize c false (ρ v)) w
  · simpa only [leaf, Set.mem_ofPred_eq, not_not] using
      (AC.cobs_dual (DeciNSSE.Tree.normalize c false (ρ v)) w).not
  · simpa only [not_not] using (leaf_minus c (ρ v) w).not.symm
  · exact (leaf_minus c (ρ v) w).symm

/-- Translate the observation to a finite ground comparison. -/
def Observation.bound {V : Type*} (c : Fin n → Bool) (o : Observation n V) :
    GroundBound n V :=
  let b := o.normalized.bound
  ⟨b.var, b.lower, FTree.normalize c false b.tree⟩

/-- The finite mixed ground bound is equivalent to its path observation. -/
theorem observation_bound_mixed {V : Type*} (c : Fin n → Bool)
    (ρ : V → DeciNSSE.Tree n) (o : Observation n V) :
    (o.bound c).Holds c ρ ↔ o.Holds c ρ := by
  rw [← observation_normalized, ← Full.observation_bound]
  simp only [Observation.bound, GroundBound.Holds, FTree.normalize_toTree]
  simp only [DeciNSSE.treeLe_false_iff_le]
  simp only [DeciNSSE.treeLe_iff_normalize, DeciNSSE.normalize_involutive]

/-- The zero-, one-, or two-pin realization obligation. A proof may flatten
the observation pins to finite ground bounds and apply regular satisfiability
or finite-bound pinning. -/
def TwoObservationRealization {V : Type*} (C : DeciNSSE.Tree n → Prop) (c : Fin n → Bool)
    (χ : List (LitT n V)) : Prop :=
  ∀ ρ, SatT c ρ χ → ∀ O : List (Observation n V), O.length ≤ 2 →
    (∀ o ∈ O, o.Holds c ρ) →
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ χ ∧ ∀ o ∈ O, o.Holds c τ

/-- Extensible visible tuples in the class admit hidden witnesses in the class.
The regular proof pins graph equations; the finite proof pins both bounds of
each visible finite tree. -/
def ClassExtension {X Z : Type*} (C : DeciNSSE.Tree n → Prop) (c : Fin n → Bool)
    (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ ρ, (∀ x, C (ρ x)) → (∃ σ, SatT c (Sum.elim ρ σ) ψ) →
    ∃ σ, (∀ z, C (σ z)) ∧ SatT c (Sum.elim ρ σ) ψ

/-- Realizing an empty observation list gives a solution in the class. -/
theorem TwoObservationRealization.satisfiable {V : Type*}
    {C : DeciNSSE.Tree n → Prop} {c : Fin n → Bool}
    {χ : List (LitT n V)} (h : TwoObservationRealization C c χ)
    (hs : (∃ ρ, SatT c ρ χ)) : SatisfiableIn C c χ := by
  obtain ⟨ρ, hρ⟩ := hs
  obtain ⟨τ, hc, ht, _⟩ := h ρ hρ [] (by simp) (by simp)
  exact ⟨τ, hc, ht⟩

/-- The two-observation lemma supplies the entire reverse-transfer argument. -/
theorem existsEntailsTIn_iff_of_transfer {X Z : Type*}
    {C : DeciNSSE.Tree n → Prop} {c : Fin n → Bool}
    {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (hφ : TwoObservationRealization C c φ) (hψ : ClassExtension C c ψ) :
    ExistsEntailsTIn C c φ ψ ↔ ExistsEntailsT c φ ψ := by
  classical
  constructor
  · intro he ρ _ hs
    by_contra hn
    have hne : ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
      rintro ⟨σ, hσ⟩; exact hn ⟨σ, fun _ => trivial, hσ⟩
    obtain ⟨O, hO, hρ, hobs⟩ := two_observations_mixed ρ hne
    obtain ⟨τ, hc, ht, hp⟩ := hφ ρ hs O hO hρ
    obtain ⟨σ, _, hσ⟩ := he τ hc ht
    exact hobs τ hp ⟨σ, hσ⟩
  · intro he ρ hc hs
    obtain ⟨σ, _, hσ⟩ := he ρ (fun _ => trivial) hs
    exact hψ ρ hc ⟨σ, hσ⟩

/-- Observation realization and class extension transfer regular entailment. -/
theorem reg_iff_of_transfer {X Z : Type*} {c : Fin n → Bool}
    {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (hφ : TwoObservationRealization RegularTop c φ)
    (hψ : ClassExtension RegularTop c ψ) :
    ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ := by
  rw [existsEntailsTReg_iff]
  exact existsEntailsTIn_iff_of_transfer hφ hψ

/-- The exact finite dispatch, conditional on the pinning/extension obligations. -/
theorem fin_dispatch_of_transfer {X Z : Type*} {c : Fin n → Bool}
    {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (hφ : SatisfiableIn FiniteTop c φ → TwoObservationRealization FiniteTop c φ)
    (hψ : SatisfiableIn FiniteTop c ψ → ClassExtension FiniteTop c ψ) :
    ExistsEntailsTFin c φ ψ ↔
      ¬ SatisfiableIn FiniteTop c φ ∨
        (SatisfiableIn FiniteTop c ψ ∧ ExistsEntailsT c φ ψ) := by
  classical
  rw [existsEntailsTFin_iff]
  change ExistsEntailsTIn FiniteTop c φ ψ ↔ _
  by_cases hsφ : SatisfiableIn FiniteTop c φ
  · constructor
    · intro he
      have hpφ := hφ hsφ
      obtain ⟨ρ, hc, hs⟩ := hsφ
      obtain ⟨σ, hσc, hσ⟩ := he ρ hc hs
      have hsψ : SatisfiableIn FiniteTop c ψ :=
        ⟨Sum.elim ρ σ, (by intro v; cases v <;> simp_all), hσ⟩
      exact Or.inr ⟨hsψ, (existsEntailsTIn_iff_of_transfer hpφ (hψ hsψ)).mp he⟩
    · rintro (hn | ⟨hsψ, he⟩)
      · exact (hn hsφ).elim
      · exact (existsEntailsTIn_iff_of_transfer (hφ hsφ) (hψ hsψ)).mpr he
  · constructor
    · intro _; exact Or.inl hsφ
    · intro _ ρ hc hs; exact (hsφ ⟨ρ, hc, hs⟩).elim

/-- Every jointly realizable finite list of ground bounds has a solution in the class. -/
def BoundRealization {V : Type*} (C : DeciNSSE.Tree n → Prop) (c : Fin n → Bool)
    (χ : List (LitT n V)) : Prop :=
  ∀ B : List (GroundBound n V),
    (∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, b.Holds c ρ) →
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ χ ∧ ∀ b ∈ B, b.Holds c τ

/-- Ground-bound realization supplies realization of at most two observations. -/
theorem BoundRealization.observations {V : Type*} {C : DeciNSSE.Tree n → Prop} {c : Fin n → Bool}
    {χ : List (LitT n V)} (h : BoundRealization C c χ) : TwoObservationRealization C c χ := by
  intro ρ hs O _ ho
  obtain ⟨τ, hc, ht, hb⟩ := h (O.map (Observation.bound c))
    ⟨ρ, hs, by simpa only [List.forall_mem_map, observation_bound_mixed] using ho⟩
  exact ⟨τ, hc, ht, by simpa only [List.forall_mem_map, observation_bound_mixed] using hb⟩

end DeciENSSE.Core.Mixed
