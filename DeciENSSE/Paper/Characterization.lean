import DeciENSSE.Core.Mixed.Conditions

/-! # Paper contract: The Characterization

Contract entries for the section *The Characterization* (`sec:ch`): existential entailment
when a system is unsatisfiable, the three conditions on single seeds that characterize it
when both systems are satisfiable (`thm:ch-characterization`), and the pure forms of the
conditions (`lem:ch-pure`).
-/
namespace DeciENSSE.Paper
open DeciNSSE Core.Full Core.Mixed
variable {n : ℕ} {X Z : Type*} {c : Fin n → Bool}
  {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

/-- **Theorem (Characterization)**, `thm:ch-characterization`(1).
Form: Visible and hidden carriers need not be finite.
-/
theorem thm_ch_characterization_1 :
    ((¬ ∃ ρ, SatT c ρ φ) → ExistsEntailsT c φ ψ) ∧
    ((∃ ρ, SatT c ρ φ) → (¬ ∃ ρ, SatT c ρ ψ) → ¬ ExistsEntailsT c φ ψ) :=
  ⟨existsEntailsT_of_unsat, not_existsEntailsT_of_unsat⟩

/-- **Theorem (Characterization)**, `thm:ch-characterization`(2).
Form: Includes the unnumbered satisfiability-dispatch equivalence. Visible and hidden carriers need not be finite.
-/
theorem thm_ch_characterization_2 :
    ((∃ ρ, SatT c ρ φ) → (∃ ρ, SatT c ρ ψ) →
      (ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ)) ∧
    (ExistsEntailsT c φ ψ ↔ (¬ ∃ ρ, SatT c ρ φ) ∨
      ((∃ ρ, SatT c ρ ψ) ∧ CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ)) := by
  refine ⟨three_conditions_mixed, ?_⟩
  classical
  by_cases hφ : ∃ ρ, SatT c ρ φ
  · by_cases hψ : ∃ ρ, SatT c ρ ψ
    · simpa only [hφ, hψ, not_true_eq_false, false_or, true_and] using
        three_conditions_mixed (ψ := ψ) hφ hψ
    · simp only [hφ, hψ, not_true_eq_false, false_or, false_and,
        iff_false]
      exact not_existsEntailsT_of_unsat hφ hψ
  · simp only [hφ, not_false_eq_true, true_or, iff_true]
    exact existsEntailsT_of_unsat hφ

/-- **Lemma (Pure forms)**, `lem:ch-pure`(1).
Form: Visible and hidden carriers need not be finite.
-/
theorem lem_ch_pure_1 : CondU c φ ψ ↔
    ¬ ∃ (p : X) (s : Bool) (u α : List (Fin n)) (e : Config n (X ⊕ Z)),
      Live c φ (p, s, u) ∧ Neg ψ e ∧ Moves c ψ (visible (p, s, u ++ α)) e := by
  constructor
  · intro h ⟨p, s, u, α, e, hl, hn, hm⟩
    exact h (p, s, u) hl e hn (reach_iff_moves.mpr ⟨α, hm⟩)
  · intro h ⟨p, s, u⟩ hl e hn hr
    obtain ⟨α, hm⟩ := reach_iff_moves.mp hr
    exact h ⟨p, s, u, α, e, hl, hn, hm⟩

/-- **Lemma (Pure forms)**, `lem:ch-pure`(2).
Form: Visible and hidden carriers need not be finite.
-/
theorem lem_ch_pure_2 : CondII c φ ψ ↔
    ∀ a b : Config n X, Live c φ a →
      Moves c ψ (visible a) (visible b) → b ∈ Cl c φ a :=
  condII_iff_moves

end DeciENSSE.Paper
