import DeciENSSE.NSSE

/-! # Plain entailment in the three tree classes

Plain entailment `φ ⊨ x ≤ y` is existential entailment with no hidden variables and the
consequent `x ≤ y` (`DeciENSSE.query`). The consequent has the solution `x = y = ⊥` in every
tree class, so the transfer theorems for existential entailment specialize as follows: regular
and arbitrary plain entailment agree, and finite plain entailment holds exactly when the
antecedent has no finite solution or arbitrary plain entailment holds. These are the two
equivalences of the paper's `cor:as-plain`. The antecedent is a flat system and may contain
copy literals `u ≤ v`.

## Main declarations

- `satFin_toCoreFull`: finite satisfiability of a flat system in the core syntax.
- `existsEntailsReg_query_iff`, `existsEntailsFin_query_iff`: the two equivalences.
-/

namespace DeciENSSE
open DeciNSSE

variable {n k : ℕ}

/-- A flat system has a finite solution in the core syntax exactly when it has a solution by
finite terms. -/
theorem satFin_toCoreFull (c : Fin n → Bool) (φ : EConstraint n k) :
    Core.Full.SatFin c (φ.map toCoreFull) ↔ ∃ ρ : V k → FTree n, ESat c (FTree.toTree ∘ ρ) φ := by
  constructor
  · rintro ⟨ρ, hρ, hs⟩
    choose g hg using hρ
    have he : FTree.toTree ∘ g = ρ := funext hg
    exact ⟨g, he ▸ (sat_toCoreFull c ρ φ).mp hs⟩
  · rintro ⟨g, hs⟩
    exact ⟨FTree.toTree ∘ g, fun v => ⟨g v, rfl⟩, (sat_toCoreFull c _ φ).mpr hs⟩

/-- The consequent `x ≤ y` has the finite solution `x = y = ⊥`. -/
theorem satFin_query (c : Fin n → Bool) (x y : V k) :
    Core.Full.SatFin c (splitFull (query (n := n) x y)) := by
  refine ⟨fun _ => Tree.bot, fun _ => ⟨FTree.bot, rfl⟩, ?_⟩
  have he : (fun _ : Fin k ⊕ Fin 0 => (Tree.bot : Tree n)) =
      Sum.elim (fun _ => Tree.bot) (fun _ => Tree.bot) := by
    funext v; cases v <;> rfl
  rw [he, sat_splitFull, sat_query]
  exact treeLe_refl c _

/-- **Regular plain entailment** (`cor:as-plain`): over regular trees, plain entailment is
plain entailment over arbitrary trees. -/
theorem existsEntailsReg_query_iff (c : Fin n → Bool) (φ : EConstraint n k) (x y : V k) :
    ExistsEntailsReg c φ (query x y) ↔ ExistsEntails c φ (query x y) := by
  rw [existsEntailsReg_iff_core, existsEntails_iff_core]
  exact Core.Mixed.existsEntailsTReg_iff_mixed _ _ _

/-- **Finite plain entailment** (`cor:as-plain`): over finite trees, plain entailment holds
exactly when the antecedent has no finite solution or plain entailment holds over arbitrary
trees. -/
theorem existsEntailsFin_query_iff (c : Fin n → Bool) (φ : EConstraint n k) (x y : V k) :
    ExistsEntailsFin c φ (query x y) ↔
      (¬ ∃ ρ : V k → FTree n, ESat c (FTree.toTree ∘ ρ) φ) ∨ ExistsEntails c φ (query x y) := by
  rw [existsEntailsFin_iff_core, existsEntails_iff_core, Core.Mixed.existsEntailsTFin_iff_mixed,
    satFin_toCoreFull]
  exact or_congr_right (and_iff_right (satFin_query c x y))

end DeciENSSE
