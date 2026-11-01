import DeciENSSE.Core.Mixed.Duality

/-! # Three conditions for mixed existential entailment

Existential entailment reduces to three conditions on the least closures
of satisfiable systems, for arbitrary variance and every arity.

## Main declarations

- `CondI0`, `CondU`, `CondII`,
  `existsEntailsT_of_unsat`, `not_existsEntailsT_of_unsat`,
  `three_conditions_mixed`, `condII_iff_moves`.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} {c : Fin n → Bool}
  {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

/-- The consequent's visible unit consequences are already forced. -/
def CondI0 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  restrict (Mu c ψ) ⊆ Mu c φ

/-- No live visible seed reaches a consequent negative unit. -/
def CondU (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ a, Live c φ a → ∀ n, Neg ψ n → ¬ Reach c ψ (visible a) n

/-- Every visible consequence of a live seed is already in its closure. -/
def CondII (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ a, Live c φ a → ∀ b : Config n X,
    Reach c ψ (visible a) (visible b) → b ∈ Cl c φ a

/-- An unsatisfiable antecedent entails every existential consequent. -/
theorem existsEntailsT_of_unsat (hφ : ¬ ∃ ρ, SatT c ρ φ) : ExistsEntailsT c φ ψ := by
  intro ρ _ hρ
  exact (hφ ⟨ρ, hρ⟩).elim

/-- A satisfiable antecedent cannot entail an unsatisfiable consequent. -/
theorem not_existsEntailsT_of_unsat (hφ : ∃ ρ, SatT c ρ φ)
    (hψ : ¬ ∃ ρ, SatT c ρ ψ) : ¬ ExistsEntailsT c φ ψ := by
  intro h
  obtain ⟨ρ, hρ⟩ := hφ
  obtain ⟨σ, _, hσ⟩ := h ρ (fun _ => trivial) hρ
  exact hψ ⟨Sum.elim ρ σ, hσ⟩

/-- The least positive closure is a model when the system is satisfiable. -/
theorem sol_mu {V : Type*} {χ : List (LitT n V)} (hχ : ∃ ρ, SatT c ρ χ) :
    Sol c χ (Mu c χ) :=
  ⟨hull_closed _, (fun {_} => hull_facts _),
    (sat_iff_mu.mp hχ).1, (sat_iff_mu.mp hχ).2⟩

/-- A live singleton's least closure is itself a model. -/
theorem sol_cl {V : Type*} {χ : List (LitT n V)} {a : Config n V}
    (ha : Live c χ a) : Sol c χ (Cl c χ a) :=
  ⟨hull_closed _, (fun {_} => hull_facts _), (live_iff.mp ha).1, (live_iff.mp ha).2⟩

/-- Necessity: apply entailment to the least model. -/
theorem condI0_of_existsEntailsT (hφ : ∃ ρ, SatT c ρ φ)
    (h : ExistsEntailsT c φ ψ) : CondI0 c φ ψ := by
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_mu hφ)
  intro a ha
  rw [← he]
  exact mu_subset hT ha

/-- Necessity: a singleton extension avoids every negative unit. -/
theorem condU_of_existsEntailsT (h : ExistsEntailsT c φ ψ) : CondU c φ ψ := by
  intro a ha n hn hr
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_cl ha)
  have hat : visible a ∈ T := by
    change a ∈ restrict T
    rw [he]
    exact mem_cl.mpr (Or.inr .refl)
  exact hT.avoids (hr.mem_of_closed hT.closed hat) hn

/-- Necessity: restrict the extension of the singleton's least model. -/
theorem condII_of_existsEntailsT (h : ExistsEntailsT c φ ψ) : CondII c φ ψ := by
  intro a ha b hr
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_cl ha)
  have hat : visible a ∈ T := by
    change a ∈ restrict T
    rw [he]
    exact mem_cl.mpr (Or.inr .refl)
  rw [← he]
  exact hr.mem_of_closed hT.closed hat

/-- Separate unit ancestry from visible-seed ancestry in a projected closure. -/
theorem mem_hull_visible {S : Set (Config n X)} {b : Config n (X ⊕ Z)} :
    b ∈ Hull c ψ (visible '' S) ↔
      b ∈ Mu c ψ ∨ ∃ a ∈ S, Reach c ψ (visible a) b := by
  constructor
  · rintro ⟨f, hf | ⟨a, ha, rfl⟩, hr⟩
    · exact Or.inl (mem_mu.mpr ⟨f, hf, hr⟩)
    · exact Or.inr ⟨a, ha, hr⟩
  · rintro (hm | ⟨a, ha, hr⟩)
    · obtain ⟨f, hf, hr⟩ := mem_mu.mp hm
      exact ⟨f, Or.inl hf, hr⟩
    · exact ⟨visible a, Or.inr ⟨a, ha, rfl⟩, hr⟩

/-- (I0) and (II) prevent new visible facts in the candidate extension. -/
theorem restrict_hull_subset (hI : CondI0 c φ ψ) (hII : CondII c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) :
    restrict (Hull c ψ (visible '' S)) ⊆ S := by
  intro b hb
  rcases mem_hull_visible.mp hb with hm | ⟨a, ha, hr⟩
  · exact mu_subset hS (hI hm)
  · exact cl_subset hS ha (hII a ⟨S, hS, ha⟩ b hr)

/-- Every negative-unit hit has one ancestor. -/
theorem avoids_hull_visible (hψ : ∃ ρ, SatT c ρ ψ) (hU : CondU c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) : Avoids ψ (Hull c ψ (visible '' S)) := by
  intro n hn hneg
  rcases mem_hull_visible.mp hn with hm | ⟨a, ha, hr⟩
  · exact (sat_iff_mu.mp hψ).1 hm hneg
  · exact hU a ⟨S, hS, ha⟩ n hneg hr

/-- A unit/seed collision returns a forced opposite visible descendant. -/
theorem no_unit_seed_collision (hI : CondI0 c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S)
    {q : X} {s : Bool} {u : List (Fin n)} (ha : (q, s, u) ∈ S)
    {v : X ⊕ Z} {t : Bool} {w : List (Fin n)}
    (hm : (v, t, w) ∈ Mu c ψ)
    (hr : Reach c ψ (visible (q, s, u)) (v, !t, w)) : False := by
  obtain ⟨f, hf, hfr⟩ := mem_mu.mp hm
  obtain ⟨δ, hδ⟩ := collision_return hfr hr
  have hforce : (q, !s, u ++ δ) ∈ Mu c φ := hI (mem_mu.mpr ⟨f, hf, hδ⟩)
  exact hS.consistent.not_flip
    ((reach_extend q s u δ).mem_of_closed hS.closed ha) (mu_subset hS hforce)

/-- Paired rules reduce every two-seed exclusion to (I0) or (II). -/
theorem consistent_hull_visible (hψ : ∃ ρ, SatT c ρ ψ)
    (hI : CondI0 c φ ψ) (hII : CondII c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) : Consistent (Hull c ψ (visible '' S)) := by
  intro p q hpq hp hq
  cases hpq with
  | pair v w =>
    rcases mem_hull_visible.mp hp with hmp | ⟨a, ha, hra⟩ <;>
      rcases mem_hull_visible.mp hq with hmq | ⟨b, hb, hrb⟩
    · exact (sat_iff_mu.mp hψ).2 (.pair v w) hmp hmq
    · rcases b with ⟨q, s, u⟩
      exact no_unit_seed_collision hI hS hb hmp hrb
    · rcases a with ⟨q, s, u⟩
      exact no_unit_seed_collision hI hS ha hmq hra
    · rcases b with ⟨q, s, u⟩
      obtain ⟨δ, hδ⟩ := collision_return hra hrb
      have hret := hII a ⟨S, hS, ha⟩ (q, !s, u ++ δ) hδ
      exact hS.consistent.not_flip
        ((reach_extend q s u δ).mem_of_closed hS.closed hb) (cl_subset hS ha hret)

/-- Sufficiency: the least closure of all visible seeds is an extension. -/
theorem existsEntailsT_of_three_conditions (hψ : ∃ ρ, SatT c ρ ψ)
    (hI : CondI0 c φ ψ) (hU : CondU c φ ψ) (hII : CondII c φ ψ) :
    ExistsEntailsT c φ ψ := by
  intro ρ _ hρ
  have hS := (sat_iff_sol ρ).mp hρ
  obtain ⟨σ, hσ⟩ := (extends_iff_hull ρ ψ).mpr
    ⟨avoids_hull_visible hψ hU hS, consistent_hull_visible hψ hI hII hS,
      restrict_hull_subset hI hII hS⟩
  exact ⟨σ, fun _ => trivial, hσ⟩

/-- The exact mixed leaf-Horn characterization. -/
theorem three_conditions_mixed (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ := by
  constructor
  · intro h
    exact ⟨condI0_of_existsEntailsT hφ h, condU_of_existsEntailsT h,
      condII_of_existsEntailsT h⟩
  · rintro ⟨hI, hU, hII⟩
    exact existsEntailsT_of_three_conditions hψ hI hU hII

/-- Move extensions to the seed, preserving liveness and shrinking closure. No antecedent
satisfiability premise is needed. -/
theorem condII_iff_moves : CondII c φ ψ ↔
    ∀ a b : Config n X, Live c φ a →
      Moves c ψ (visible a) (visible b) → b ∈ Cl c φ a := by
  constructor
  · intro h a b ha hr
    exact h a ha b (moves_reach hr)
  · intro h a ha b hr
    rcases a with ⟨p, s, u⟩
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    exact cl_extend_subset p s u α (h (p, s, u ++ α) b (live_extend α ha) hα)

/-! ## Semantic examples at ternary mixed variance -/

end DeciENSSE.Core.Mixed
