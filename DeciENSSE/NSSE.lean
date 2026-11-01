import DeciENSSE.Main

/-! # Subtype entailment as existential entailment

Ordinary entailment is a singleton visible query with no hidden variables.

## Main declarations

- `nsse_iff_ensse`, `nsseReg_iff_ensseReg`, `nsseFin_iff_ensseFin`: reductions.
- `decideEntails`, `decideEntailsReg`, `decideEntailsFin`: the ordinary subtype API.
- `EntailsTopFree`, `EntailsTopFreeReg`, `EntailsTopFreeFin`: top-free subtype semantics.
- `decideEntailsTopFree`, `decideEntailsTopFreeReg`, `decideEntailsTopFreeFin`: bonus decisions.
- The six `_correct` theorems characterize their Boolean answers.
-/

namespace DeciENSSE
open DeciNSSE

/-- Unrestricted subtype entailment is a query with no hidden variables. -/
theorem nsse_iff_ensse {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k) (x y : V k) :
    Entails c φ x y ↔ ExistsEntailsAny (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [Entails, ExistsEntailsAny, sat_lift, sat_query]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Regular subtype entailment is a query with no hidden variables. -/
theorem nsseReg_iff_ensseReg {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsReg c φ x y ↔ ExistsEntailsAnyReg (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [EntailsReg, ExistsEntailsAnyReg, sat_lift, sat_query, Function.comp_apply]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Finite subtype entailment is a query with no hidden variables. -/
theorem nsseFin_iff_ensseFin {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsFin c φ x y ↔ ExistsEntailsAnyFin (h := 0) c (liftConstraint φ) (query x y) := by
  simp only [EntailsFin, ExistsEntailsAnyFin, sat_lift, sat_query, Function.comp_apply]
  constructor
  · intro H ρ hs; exact ⟨Fin.elim0, H ρ hs⟩
  · intro H ρ hs; exact (H ρ hs).choose_spec

/-- Covariant entailment restricted to top-free assignments. -/
def EntailsTopFree {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ, (∀ v, TopFree (ρ v)) → BFSat ρ φ →
    DeciNSSE.Tree.Le (fun _ => false) (ρ x) (ρ y)

/-- Top-free subtype entailment is a query with no hidden variables. -/
theorem topFree_nsse_iff_ensse {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFree φ x y ↔ ExistsEntails (h := 0) φ
      [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)] := by
  constructor
  · intro H ρ hρ hs
    refine ⟨Fin.elim0, (fun z => Fin.elim0 z), ?_⟩
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left] using H ρ hρ hs
  · intro H ρ hρ hs
    obtain ⟨σ, _, Hσ⟩ := H ρ hρ hs
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left] using Hσ

/-- Top-free subtype entailment over regular graphs. -/
def EntailsTopFreeReg {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ : V k → RGraph n,
    (∀ v, TopFree (ρ v).unfold) → BFSat (RGraph.unfold ∘ ρ) φ →
    DeciNSSE.Tree.Le (fun _ => false) ((ρ x).unfold) ((ρ y).unfold)

/-- Top-free subtype entailment is a query with no hidden variables. -/
theorem topFree_nsseReg_iff_ensseReg {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFreeReg φ x y ↔ ExistsEntailsReg (h := 0) φ
      [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)] := by
  constructor
  · intro H ρ hρ hs
    refine ⟨Fin.elim0, (fun z => Fin.elim0 z), ?_⟩
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left,
      Function.comp_apply] using H ρ hρ hs
  · intro H ρ hρ hs
    obtain ⟨σ, _, Hσ⟩ := H ρ hρ hs
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left,
      Function.comp_apply] using Hσ

/-- Top-free subtype entailment over finite terms. -/
def EntailsTopFreeFin {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ : V k → FTree n,
    (∀ v, TopFree (ρ v).toTree) → BFSat (FTree.toTree ∘ ρ) φ →
    DeciNSSE.Tree.Le (fun _ => false) ((ρ x).toTree) ((ρ y).toTree)

/-- Top-free subtype entailment is a query with no hidden variables. -/
theorem topFree_nsseFin_iff_ensseFin {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    EntailsTopFreeFin φ x y ↔ ExistsEntailsFin (h := 0) φ
      [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)] := by
  constructor
  · intro H ρ hρ hs
    refine ⟨Fin.elim0, (fun z => Fin.elim0 z), ?_⟩
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left,
      Function.comp_apply] using H ρ hρ hs
  · intro H ρ hρ hs
    obtain ⟨σ, _, Hσ⟩ := H ρ hρ hs
    simpa only [BFSat, List.map_cons, List.map_nil, BFLit.toELit, ESat,
      List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left,
      Function.comp_apply] using Hσ

/-- Decide arbitrary-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntails {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.Entails c φ x y) := by
  letI := decideExistsEntailsAny (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsse_iff_ensse c φ x y).symm

/-- The decision returns true exactly when arbitrary-tree subtype entailment holds. -/
theorem decideEntails_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntails c φ x y) = true ↔ DeciNSSE.Entails c φ x y :=
  @decide_eq_true_iff _ (decideEntails c φ x y)

/-- Decide regular-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntailsReg {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsReg c φ x y) := by
  letI := decideExistsEntailsAnyReg (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsseReg_iff_ensseReg c φ x y).symm

/-- The decision returns true exactly when regular-tree subtype entailment holds. -/
theorem decideEntailsReg_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsReg c φ x y) = true ↔ DeciNSSE.EntailsReg c φ x y :=
  @decide_eq_true_iff _ (decideEntailsReg c φ x y)

/-- Decide finite-tree subtype entailment through existential entailment. -/
@[instance_reducible] def decideEntailsFin {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsFin c φ x y) := by
  letI := decideExistsEntailsAnyFin (h := 0) c (liftConstraint φ) (query x y)
  exact decidable_of_iff _ (nsseFin_iff_ensseFin c φ x y).symm

/-- The decision returns true exactly when finite-tree subtype entailment holds. -/
theorem decideEntailsFin_correct {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsFin c φ x y) = true ↔ DeciNSSE.EntailsFin c φ x y :=
  @decide_eq_true_iff _ (decideEntailsFin c φ x y)

/-- Decide top-free covariant subtype entailment over arbitrary trees. -/
@[instance_reducible] def decideEntailsTopFree {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFree φ x y) := by
  letI := decideExistsEntails (h := 0) φ
    [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]
  exact decidable_of_iff _ (topFree_nsse_iff_ensse φ x y).symm

/-- The decision returns true exactly when top-free arbitrary-tree entailment holds. -/
theorem decideEntailsTopFree_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFree φ x y) = true ↔ EntailsTopFree φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFree φ x y)

/-- Decide top-free covariant subtype entailment over regular trees. -/
@[instance_reducible] def decideEntailsTopFreeReg {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFreeReg φ x y) := by
  letI := decideExistsEntailsReg (h := 0) φ
    [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]
  exact decidable_of_iff _ (topFree_nsseReg_iff_ensseReg φ x y).symm

/-- The decision returns true exactly when top-free regular-tree entailment holds. -/
theorem decideEntailsTopFreeReg_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFreeReg φ x y) = true ↔ EntailsTopFreeReg φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFreeReg φ x y)

/-- Decide top-free covariant subtype entailment over finite trees. -/
@[instance_reducible] def decideEntailsTopFreeFin {n k : ℕ} (φ : BFConstraint n k)
    (x y : V k) : Decidable (EntailsTopFreeFin φ x y) := by
  letI := decideExistsEntailsFin (h := 0) φ
    [BFLit.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]
  exact decidable_of_iff _ (topFree_nsseFin_iff_ensseFin φ x y).symm

/-- The decision returns true exactly when top-free finite-tree entailment holds. -/
theorem decideEntailsTopFreeFin_correct {n k : ℕ} (φ : BFConstraint n k) (x y : V k) :
    @decide _ (decideEntailsTopFreeFin φ x y) = true ↔ EntailsTopFreeFin φ x y :=
  @decide_eq_true_iff _ (decideEntailsTopFreeFin φ x y)

end DeciENSSE
