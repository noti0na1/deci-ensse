import DeciENSSE.Core.Full.TopGraphs
import DeciENSSE.Core.Mixed.Final
import DeciENSSE.Core.Mixed.FinitePinning
import DeciENSSE.Support.Nullary.Decide
import DeciNSSE.Semantics.Characterization
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Regular realization and entailment

At most two observations retain a failure of extension. Realizing those
observations and pinning visible graph equations transfers existential
entailment between arbitrary and regular trees.

## Main declarations

- `two_observations_mixed`
- `regular_bound_realization`
- `regular_class_extension`
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

/-- Failure of extension is retained by at most two observations (repeat a
unary witness). Satisfiability excludes obstructions supported only by facts. -/
theorem two_observations_mixed {X Z : Type*} {c : Fin n → Bool}
    {ψ : List (LitT n (X ⊕ Z))} (hψ : ∃ τ, SatT c τ ψ)
    (ρ : X → DeciNSSE.Tree n) (hne : ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) :
    ∃ a b : Observation n X, a.Holds c ρ ∧ b.Holds c ρ ∧
      ∀ ρ', a.Holds c ρ' → b.Holds c ρ' →
        ¬ ∃ σ, SatT c (Sum.elim ρ' σ) ψ := by
  classical
  obtain ⟨δ, hδ⟩ := hψ
  have hd := (sat_iff_sol δ).mp hδ
  by_cases hn : Avoids ψ (Hull c ψ (visibleSeeds c ρ))
  · by_cases hc : Consistent (Hull c ψ (visibleSeeds c ρ))
    · have hv : ¬ restrict (Hull c ψ (visibleSeeds c ρ)) ⊆ configSet c ρ :=
        fun hv => hne ((extends_iff_hull ρ ψ).mpr ⟨hn, hc, hv⟩)
      obtain ⟨b, hb, hnb⟩ := Set.not_subset.mp hv
      rcases hull_ancestor hb with hf | ⟨a, ha, hp⟩
      · refine ⟨(b, false), (b, false), hnb, hnb, ?_⟩
        rintro ρ' hno _ ⟨σ, hs⟩
        exact hno (hf _ hs)
      · refine ⟨a, (b, false), ha, hnb, ?_⟩
        rintro ρ' ha' hno ⟨σ, hs⟩
        exact hno (hp ρ' σ ha' hs)
    · simp only [Consistent] at hc
      push Not at hc
      obtain ⟨p, q, hpq, hp, hq, _⟩ := hc
      rcases hull_ancestor hp with hf | ⟨a, ha, hpa⟩ <;>
        rcases hull_ancestor hq with hg | ⟨b, hb, hpb⟩
      · exact (hd.consistent hpq (hf δ hδ) (hg δ hδ)).elim
      · refine ⟨b, b, hb, hb, ?_⟩
        rintro ρ' hb' _ ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq (hf _ hs) (hpb ρ' σ hb' hs)
      · refine ⟨a, a, ha, ha, ?_⟩
        rintro ρ' ha' _ ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq (hpa ρ' σ ha' hs) (hg _ hs)
      · refine ⟨a, b, ha, hb, ?_⟩
        rintro ρ' ha' hb' ⟨σ, hs⟩
        exact ((sat_iff_sol _).mp hs).consistent hpq
          (hpa ρ' σ ha' hs) (hpb ρ' σ hb' hs)
  · simp only [Avoids, not_forall, not_not] at hn
    obtain ⟨p, hp, hneg⟩ := hn
    rcases hull_ancestor hp with hf | ⟨a, ha, hpa⟩
    · exact (hd.avoids (hf δ hδ) hneg).elim
    · refine ⟨a, a, ha, ha, ?_⟩
      rintro ρ' ha' _ ⟨σ, hs⟩
      exact ((sat_iff_sol _).mp hs).avoids (hpa ρ' σ ha' hs) hneg

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
    (o.bound c).HoldsMixed c ρ ↔ o.Holds c ρ := by
  rw [← observation_normalized, ← Full.observation_bound]
  simp only [Observation.bound, GroundBound.HoldsMixed, GroundBound.Holds,
    FTree.normalize_toTree, DeciNSSE.treeLe_iff_normalize, DeciNSSE.normalize_involutive]

/-- A solution with every value in the specified tree class. -/
abbrev SatisfiableIn {V : Type*} (C : DeciNSSE.Tree n → Prop) (c : Fin n → Bool)
    (χ : List (LitT n V)) : Prop := Full.SatisfiableIn C c χ

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
theorem TwoObservationRealization.satisfiable {V : Type*} {C : DeciNSSE.Tree n → Prop} {c : Fin n →
  Bool}
    {χ : List (LitT n V)} (h : TwoObservationRealization C c χ)
    (hs : (∃ ρ, SatT c ρ χ)) : SatisfiableIn C c χ := by
  obtain ⟨ρ, hρ⟩ := hs
  obtain ⟨τ, hc, ht, _⟩ := h ρ hρ [] (by simp) (by simp)
  exact ⟨τ, hc, ht⟩

/-- The two-observation lemma supplies the entire reverse-transfer argument. -/
theorem existsEntailsTIn_iff_of_transfer {X Z : Type*} {C : DeciNSSE.Tree n → Prop} {c : Fin n →
  Bool}
    {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (hφ : TwoObservationRealization C c φ) (hψ : ClassExtension C c ψ) :
    ExistsEntailsTIn C c φ ψ ↔ ExistsEntailsT c φ ψ := by
  classical
  constructor
  · intro he ρ _ hs
    by_cases hsat : (∃ ρ, SatT c ρ ψ)
    · by_contra hn
      have hne : ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
        rintro ⟨σ, hσ⟩; exact hn ⟨σ, fun _ => trivial, hσ⟩
      obtain ⟨a, b, ha, hb, hobs⟩ := two_observations_mixed hsat ρ hne
      obtain ⟨τ, hc, ht, hp⟩ := hφ ρ hs [a,b] (by simp) (by simp [ha, hb])
      obtain ⟨σ, _, hσ⟩ := he τ hc ht
      exact hobs τ (hp a (by simp)) (hp b (by simp)) ⟨σ, hσ⟩
    · obtain ⟨τ, hc, ht, _⟩ := hφ ρ hs [] (by simp) (by simp)
      obtain ⟨σ, _, hσ⟩ := he τ hc ht
      exact (hsat ⟨Sum.elim τ σ, hσ⟩).elim
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
def BoundRealization {V : Type*} (C : DeciNSSE.Tree n → Prop) (c : Fin n → Bool) (χ : List (LitT n
  V)) : Prop :=
  ∀ B : List (GroundBound n V),
    (∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, b.HoldsMixed c ρ) →
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ χ ∧ ∀ b ∈ B, b.HoldsMixed c τ

/-- Ground-bound realization supplies realization of at most two observations. -/
theorem BoundRealization.observations {V : Type*} {C : DeciNSSE.Tree n → Prop} {c : Fin n → Bool}
    {χ : List (LitT n V)} (h : BoundRealization C c χ) : TwoObservationRealization C c χ := by
  intro ρ hs O _ ho
  obtain ⟨τ, hc, ht, hb⟩ := h (O.map (Observation.bound c))
    ⟨ρ, hs, by simpa only [List.forall_mem_map, observation_bound_mixed] using ho⟩
  exact ⟨τ, hc, ht, by simpa only [List.forall_mem_map, observation_bound_mixed] using hb⟩

/-- Regular satisfiability at every arity; nullary trees are already regular. -/
theorem satisfiable_regular {V : Type*} [Fintype V] (c : Fin n → Bool)
    {χ : List (LitT n V)} (h : ∃ ρ, SatT c ρ χ) : SatisfiableIn RegularTop c χ := by
  cases n with
  | zero =>
    obtain ⟨ρ, hρ⟩ := h
    exact ⟨ρ, fun v => Support.Nullary.unfold_zero_surjective (ρ v), hρ⟩
  | succ m => exact Full.satisfiable_regular c h

namespace Graphs
open Full.TopGraphs
variable {I V : Type*}

/-- Satisfying the graph literals is equivalent to solving its state equations. -/
theorem sat_equations [Fintype I] (c : Fin n → Bool) (g : I → RGraph n) (τ : States g →
  DeciNSSE.Tree n) :
    SatT c τ (equations g) ↔ Model g τ := by
  simp only [equations, SatT, List.forall_mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, forall_const]
  constructor
  · intro h i q
    have hh := h ⟨i,q⟩
    cases hl : (g i).label q <;>
      simp only [equationsAt, hl, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, HoldsT, rhs] at hh ⊢
    · exact hh
    · exact DeciNSSE.treeLe_antisymm hh.2 hh.1
    · exact hh
  · intro h ⟨i,q⟩
    have hh := h i q
    cases hl : (g i).label q <;>
      simp only [equationsAt, hl, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, HoldsT, rhs] at hh ⊢
    · exact hh
    · rw [hh]; exact ⟨DeciNSSE.treeLe_refl _ _, DeciNSSE.treeLe_refl _ _⟩
    · exact hh

/-- A bound between an old variable and a designated graph root. -/
abbrev Binding (V I : Type*) := V × I × Bool

/-- Interpret a comparison between a variable and a designated graph root. -/
def bindingHolds (c : Fin n → Bool) (g : I → RGraph n) (ρ : V → DeciNSSE.Tree n) (b : Binding V I) :
  Prop :=
  if b.2.2 then DeciNSSE.Tree.Le c (g b.2.1).unfold (ρ b.1) else DeciNSSE.Tree.Le c (ρ b.1) (g
    b.2.1).unfold

/-- Encode a comparison with a graph root as a flat literal. -/
def bindingLit (g : I → RGraph n) (b : Binding V I) : LitT n (V ⊕ States g) :=
  if b.2.2 then .le (.inr ⟨b.2.1, (g b.2.1).root⟩) (.inl b.1)
  else .le (.inl b.1) (.inr ⟨b.2.1, (g b.2.1).root⟩)

private theorem root_value (g : I → RGraph n) (i : I) :
    values g ⟨i,(g i).root⟩ = (g i).unfold := rfl

private theorem binding_spec (c : Fin n → Bool) (g : I → RGraph n) (τ : V ⊕ States g → DeciNSSE.Tree
  n)
    (h : τ ∘ Sum.inr = values g) (b : Binding V I) :
    HoldsT c τ (bindingLit g b) ↔ bindingHolds c g (τ ∘ Sum.inl) b := by
  have he := congrFun h ⟨b.2.1, (g b.2.1).root⟩
  simp only [Function.comp_apply, root_value] at he
  cases hb : b.2.2 <;> simp [bindingLit, bindingHolds, hb, HoldsT, he]

private theorem sat_map {A B : Type*} {c : Fin n → Bool} (f : A → B) (τ : B → DeciNSSE.Tree n) (χ :
  List (LitT n A)) :
    SatT c τ (χ.map (LitT.map f)) ↔ SatT c (τ ∘ f) χ := by
  simp [SatT]

private theorem Covariant.sat_append {A : Type*} {c : Fin n → Bool} (τ : A → DeciNSSE.Tree n) (χ ψ :
  List (LitT n A)) :
    SatT c τ (χ ++ ψ) ↔
      SatT c τ χ ∧ SatT c τ ψ := by
  simp [SatT, or_imp, forall_and]

/-- Finitely many inequalities to regular graph values can be preserved while
regularizing a satisfiable full-signature assignment. -/
theorem regularize [Fintype V] [Fintype I] (c : Fin n → Bool)
    (χ : List (LitT n V)) (g : I → RGraph n) (B : List (Binding V I))
    (hs : ∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, bindingHolds c g ρ b) :
    ∃ τ, (∀ v, RegularTop (τ v)) ∧ SatT c τ χ ∧
      ∀ b ∈ B, bindingHolds c g τ b := by
  let E : List (LitT n (V ⊕ States g)) :=
    χ.map (LitT.map Sum.inl) ++
    (equations g).map (LitT.map Sum.inr) ++ B.map (bindingLit g)
  obtain ⟨ρ, hρ, hb⟩ := hs
  have hsE : ∃ ρ, SatT c ρ E := by
    refine ⟨Sum.elim ρ (values g), ?_⟩
    simp only [E, Covariant.sat_append, sat_map]
    refine ⟨⟨hρ, (sat_equations c g _).mpr (values_model g)⟩, ?_⟩
    intro l hl
    obtain ⟨b, hbB, rfl⟩ := List.mem_map.mp hl
    exact (binding_spec c g _ rfl b).mpr (hb b hbB)
  obtain ⟨τ, hc, ht⟩ := satisfiable_regular c hsE
  simp only [E, Covariant.sat_append, sat_map] at ht
  have hv : τ ∘ Sum.inr = values g := model_unique g ((sat_equations c g _).mp ht.1.2)
  refine ⟨τ ∘ Sum.inl, fun v => hc (.inl v), ht.1.1, ?_⟩
  intro b hb
  exact (binding_spec c g τ hv b).mp (ht.2 _ (List.mem_map.mpr ⟨b, hb, rfl⟩))

end Graphs

/-- Every jointly realizable finite list of mixed ground bounds has a regular solution. -/
theorem regular_bound_realization {V : Type*} [Fintype V]
    (c : Fin n → Bool) (χ : List (LitT n V)) : BoundRealization RegularTop c χ := by
  classical
  intro B hs
  have hg : ∀ i : Fin B.length, ∃ g : RGraph n, g.unfold = (B.get i).tree.toTree := by
    intro i
    apply (Characterization.unfold_range_iff _).mpr
    exact Characterization.subtrees_finite_of_domain_finite _
      (Characterization.domain_toTree_finite (B.get i).tree)
  choose g hg using hg
  let bindings : List (Graphs.Binding V (Fin B.length)) :=
    (List.finRange B.length).map (fun i => ((B.get i).var, i, (B.get i).lower))
  have hb (ρ : V → DeciNSSE.Tree n) (i : Fin B.length) :
      Graphs.bindingHolds c g ρ ((B.get i).var, i, (B.get i).lower) ↔
        (B.get i).HoldsMixed c ρ := by
    simp only [Graphs.bindingHolds, hg, GroundBound.HoldsMixed]
  obtain ⟨ρ, hρ, hB⟩ := hs
  obtain ⟨τ, hc, ht, hτ⟩ := Graphs.regularize c χ g bindings ⟨ρ, hρ, by
    simp only [bindings, List.forall_mem_map]
    intro i _
    exact (hb ρ i).mpr (hB _ (List.get_mem B i))⟩
  refine ⟨τ, hc, ht, ?_⟩
  intro b hbB
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hbB
  exact (hb τ i).mp (hτ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))

/-- Graph equations keep the entire regular visible tuple fixed. -/
theorem regular_class_extension {X Z : Type*} [Fintype X] [Fintype Z]
    (c : Fin n → Bool) (ψ : List (LitT n (X ⊕ Z))) : ClassExtension RegularTop c ψ := by
  classical
  intro ρ hρ he
  choose g hg using hρ
  let B : List (Graphs.Binding (X ⊕ Z) X) :=
    Finset.univ.toList.flatMap fun x => [(.inl x, x, true), (.inl x, x, false)]
  obtain ⟨σ, hσ⟩ := he
  have hb : ∀ b ∈ B, Graphs.bindingHolds c g (Sum.elim ρ σ) b := by
    simp only [B, List.forall_mem_flatMap]
    intro x _
    simp [Graphs.bindingHolds, hg, DeciNSSE.treeLe_refl]
  obtain ⟨τ, hc, ht, hbτ⟩ := Graphs.regularize c ψ g B ⟨_, hσ, hb⟩
  have hv (x : X) : τ (.inl x) = ρ x := by
    have hlo := hbτ (.inl x, x, true) (by simp [B])
    have hhi := hbτ (.inl x, x, false) (by simp [B])
    change DeciNSSE.Tree.Le c (g x).unfold (τ (.inl x)) at hlo
    change DeciNSSE.Tree.Le c (τ (.inl x)) (g x).unfold at hhi
    rw [hg x] at hlo hhi
    exact DeciNSSE.treeLe_antisymm hhi hlo
  refine ⟨fun z => τ (.inr z), fun z => hc (.inr z), ?_⟩
  have heq : Sum.elim ρ (fun z => τ (.inr z)) = τ := by
    funext v; cases v with
    | inl x => exact (hv x).symm
    | inr z => rfl
  rw [heq]; exact ht

/-- Regular and arbitrary entailment coincide, with no transfer premise. -/
theorem existsEntailsTReg_iff_mixed {X Z : Type*} [Fintype X] [Fintype Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ :=
  reg_iff_of_transfer (regular_bound_realization c φ).observations
    (regular_class_extension c ψ)

/-- Computable regular-tree endpoint, with no parity premise. -/
def decideExistsEntailsAnyReg {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTReg c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsAnyReg c φ ψ
  | succ m =>
    letI := decideExistsEntailsAny c φ ψ
    exact decidable_of_iff _ (existsEntailsTReg_iff_mixed c φ ψ).symm

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideExistsEntailsAnyReg_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyReg c φ ψ) = true ↔ ExistsEntailsTReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyReg c φ ψ)

/-- At arity zero the decision agrees with direct enumeration of labels. -/
theorem decideExistsEntailsAnyReg_nullary_agrees {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin 0 → Bool) (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyReg c φ ψ) =
      @decide _ (Nullary.decideExistsEntailsAnyReg c φ ψ) := rfl

namespace RegularMixedExamples
open LeafHornExamples ConditionsExamples

/-- Every transfer obligation holds for a satisfiable ternary system. -/
theorem transfer_nonvacuous :
    SatisfiableIn RegularTop arrow mixed ∧
    BoundRealization RegularTop arrow mixed ∧
    TwoObservationRealization RegularTop arrow mixed ∧
    ClassExtension RegularTop arrow embedded :=
  ⟨satisfiable_regular arrow DualityExamples.mixed_sat,
    regular_bound_realization arrow mixed,
    (regular_bound_realization arrow mixed).observations,
    regular_class_extension arrow embedded⟩

/-- The decision procedure returns true on the ternary entailment example. -/
theorem ternary_positive :
    @decide _ (decideExistsEntailsAnyReg arrow mixed embedded) = true :=
  (decideExistsEntailsAnyReg_correct _ _ _).mpr
    ((existsEntailsTReg_iff_mixed _ _ _).mpr embedded_entails)

/-- The decision procedure returns false on the ternary entailment example. -/
theorem ternary_negative :
    @decide _ (decideExistsEntailsAnyReg arrow [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact embedded_empty_not_entails ((existsEntailsTReg_iff_mixed _ _ _).mp
    ((decideExistsEntailsAnyReg_correct _ _ _).mp h))

/-- The contravariant unary fixed point has regular hidden witnesses. -/
theorem unary_positive :
    @decide _ (decideExistsEntailsAnyReg (fun _ => true) []
      ([.lef (.inr ()) (fun _ => .inr ()), .fle (fun _ => .inr ()) (.inr ())] :
        List (LitT 1 (Unit ⊕ Unit)))) = true := by
  apply (decideExistsEntailsAnyReg_correct _ _ _).mpr
  intro ρ _
  refine ⟨fun _ => RGraph.allF 1, ?_⟩
  have h := RGraph.allF_unfold_node (n := 1)
  simp [SatT, HoldsT, Function.comp_def, ← h, DeciNSSE.treeLe_refl]

/-- The decision procedure returns true on the nullary entailment example. -/
theorem nullary_positive :
    @decide _ (decideExistsEntailsAnyReg Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = true := by decide +kernel

/-- The decision procedure returns false on the nullary entailment example. -/
theorem nullary_negative :
    @decide _ (decideExistsEntailsAnyReg Fin.elim0 []
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = false := by decide +kernel

end RegularMixedExamples

end DeciENSSE.Core.Mixed
