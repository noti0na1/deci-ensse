import DeciENSSE.Main

/-! # Subtype entailment as existential entailment

Plain subtype entailment `φ ⊨ x ≤ y` is existential entailment with no hidden variables
and the consequent `x ≤ y` (`query`). The three reductions below turn the existential
deciders of `DeciENSSE.Main` into deciders of the plain entailment `DeciNSSE.Entails` of the
shared library and of its regular and finite variants; they have the same names and types
as the deciders of deci-nsse and use no other decision procedure for plain entailment. The
same reductions, with the consequent `bfQuery`, decide covariant plain entailment over
top-free trees.

## Main declarations

- `nsse_iff_ensse`, `nsseReg_iff_ensseReg`, `nsseFin_iff_ensseFin`: plain entailment is a
  query with no hidden variables.
- `decideEntails`, `decideEntailsReg`, `decideEntailsFin`: deciders for plain entailment.
- `topFree_nsse_iff_ensse`, `topFree_nsseReg_iff_ensseReg`, `topFree_nsseFin_iff_ensseFin`:
  the same reductions over top-free trees.
- `decideEntailsTopFree`, `decideEntailsTopFreeReg`, `decideEntailsTopFreeFin`: deciders for
  covariant plain entailment over top-free trees.
- The six `_correct` theorems identify the Boolean answers with the semantics.
-/

namespace DeciENSSE
open DeciNSSE

/-- Plain subtype entailment is a query with no hidden variables. -/
theorem nsse_iff_ensse {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k) (x y : V k) :
    Entails c φ x y ↔ ExistsEntails (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [Entails, ExistsEntails, sat_lift, sat_query]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Regular subtype entailment is a query with no hidden variables. -/
theorem nsseReg_iff_ensseReg {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsReg c φ x y ↔ ExistsEntailsReg (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [EntailsReg, ExistsEntailsReg, sat_lift, sat_query, Function.comp_apply]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Finite subtype entailment is a query with no hidden variables. -/
theorem nsseFin_iff_ensseFin {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsFin c φ x y ↔ ExistsEntailsFin (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [EntailsFin, ExistsEntailsFin, sat_lift, sat_query, Function.comp_apply]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Decide arbitrary-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntails {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.Entails c φ x y) := by
  letI := decideExistsEntails (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsse_iff_ensse c φ x y).symm

/-- The decision returns true exactly when arbitrary-tree subtype entailment holds. -/
theorem decideEntails_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntails c φ x y) = true ↔ DeciNSSE.Entails c φ x y :=
  @decide_eq_true_iff _ (decideEntails c φ x y)

/-- Decide regular-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntailsReg {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsReg c φ x y) := by
  letI := decideExistsEntailsReg (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsseReg_iff_ensseReg c φ x y).symm

/-- The decision returns true exactly when regular-tree subtype entailment holds. -/
theorem decideEntailsReg_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsReg c φ x y) = true ↔ DeciNSSE.EntailsReg c φ x y :=
  @decide_eq_true_iff _ (decideEntailsReg c φ x y)

/-- Decide finite-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntailsFin {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsFin c φ x y) := by
  letI := decideExistsEntailsFin (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsseFin_iff_ensseFin c φ x y).symm

/-- The decision returns true exactly when finite-tree subtype entailment holds. -/
theorem decideEntailsFin_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsFin c φ x y) = true ↔ DeciNSSE.EntailsFin c φ x y :=
  @decide_eq_true_iff _ (decideEntailsFin c φ x y)

/-- Top-free subtype entailment is a query with no hidden variables. -/
theorem topFree_nsse_iff_ensse {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFree φ x y ↔ ExistsEntailsTopFree (h := 0) φ (bfQuery x y) := by
  simp only [EntailsTopFree, ExistsEntailsTopFree, bfSat_query]
  constructor
  · intro H ρ hρ hs; exact ⟨Fin.elim0, fun z => z.elim0, H ρ hρ hs⟩
  · intro H ρ hρ hs; exact (H ρ hρ hs).choose_spec.2

/-- Top-free regular subtype entailment is a query with no hidden variables. -/
theorem topFree_nsseReg_iff_ensseReg {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFreeReg φ x y ↔ ExistsEntailsTopFreeReg (h := 0) φ (bfQuery x y) := by
  simp only [EntailsTopFreeReg, ExistsEntailsTopFreeReg, bfSat_query, Function.comp_apply]
  constructor
  · intro H ρ hρ hs; exact ⟨Fin.elim0, fun z => z.elim0, H ρ hρ hs⟩
  · intro H ρ hρ hs; exact (H ρ hρ hs).choose_spec.2

/-- Top-free finite subtype entailment is a query with no hidden variables. -/
theorem topFree_nsseFin_iff_ensseFin {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFreeFin φ x y ↔ ExistsEntailsTopFreeFin (h := 0) φ (bfQuery x y) := by
  simp only [EntailsTopFreeFin, ExistsEntailsTopFreeFin, bfSat_query, Function.comp_apply]
  constructor
  · intro H ρ hρ hs; exact ⟨Fin.elim0, fun z => z.elim0, H ρ hρ hs⟩
  · intro H ρ hρ hs; exact (H ρ hρ hs).choose_spec.2

/-- Decide top-free covariant subtype entailment over arbitrary trees. -/
@[instance_reducible] def decideEntailsTopFree {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFree φ x y) := by
  letI := decideExistsEntailsTopFree (h := 0) φ (bfQuery x y)
  exact decidable_of_iff _ (topFree_nsse_iff_ensse φ x y).symm

/-- The decision returns true exactly when top-free arbitrary-tree entailment holds. -/
theorem decideEntailsTopFree_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFree φ x y) = true ↔ EntailsTopFree φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFree φ x y)

/-- Decide top-free covariant subtype entailment over regular trees. -/
@[instance_reducible] def decideEntailsTopFreeReg {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFreeReg φ x y) := by
  letI := decideExistsEntailsTopFreeReg (h := 0) φ (bfQuery x y)
  exact decidable_of_iff _ (topFree_nsseReg_iff_ensseReg φ x y).symm

/-- The decision returns true exactly when top-free regular-tree entailment holds. -/
theorem decideEntailsTopFreeReg_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFreeReg φ x y) = true ↔ EntailsTopFreeReg φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFreeReg φ x y)

/-- Decide top-free covariant subtype entailment over finite trees. -/
@[instance_reducible] def decideEntailsTopFreeFin {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFreeFin φ x y) := by
  letI := decideExistsEntailsTopFreeFin (h := 0) φ (bfQuery x y)
  exact decidable_of_iff _ (topFree_nsseFin_iff_ensseFin φ x y).symm

/-- The decision returns true exactly when top-free finite-tree entailment holds. -/
theorem decideEntailsTopFreeFin_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFreeFin φ x y) = true ↔ EntailsTopFreeFin φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFreeFin φ x y)

end DeciENSSE
