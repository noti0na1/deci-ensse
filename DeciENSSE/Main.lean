import Mathlib.Logic.Equiv.Fin.Basic
import DeciENSSE.Core.Main
import DeciENSSE.Semantics
import DeciENSSE.Core.Full.Bridge

/-! # Decidable existential subtype entailment

Finite-index constraints are converted to the core's visible and hidden sum
carriers. The conversions preserve literal satisfaction and both quantifiers.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`: top-free decisions.
- `decideExistsEntailsAny`, `decideExistsEntailsAnyReg`, `decideExistsEntailsAnyFin`:
  full-signature decisions.
- The six `_correct` theorems identify the Boolean answers with their semantics.
- `toCoreFull`, `splitFull`, `toCoreBF`, `splitBF`: computable syntax conversions.
- `existsEntailsAny_iff_core`: arbitrary-tree semantics agree.
- `existsEntailsAnyReg_iff_core`, `existsEntailsAnyFin_iff_core`: class semantics agree.
-/

namespace DeciENSSE
open DeciNSSE

/-- Convert a full-signature literal to the core syntax. -/
def toCoreFull {n k : ℕ} : ELit n k → Core.Full.LitT n (Fin k)
  | .le x y => .le x y
  | .leF x a => .lef x a
  | .fLe a x => .fle a x
  | .eqBot x => .bot x
  | .eqTop x => .top x

/-- Separate the visible and hidden indices of a consequent. -/
def splitFull {n k h : ℕ} (ψ : EConstraint n (k + h)) :
    List (Core.Full.LitT n (Fin k ⊕ Fin h)) :=
  ψ.map fun l => (toCoreFull l).map finSumFinEquiv.symm

/-- Literal conversion preserves satisfaction. -/
@[simp] theorem holds_toCoreFull {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Tree n) (l : ELit n k) :
    Core.Full.HoldsT c ρ (toCoreFull l) ↔ l.holds c ρ := by
  cases l <;> rfl

/-- Conjunction conversion preserves satisfaction. -/
@[simp] theorem sat_toCoreFull {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Tree n) (φ : EConstraint n k) :
    Core.Full.SatT c ρ (φ.map toCoreFull) ↔ ESat c ρ φ := by
  simp [Core.Full.SatT, ESat]

/-- Joining assignments agrees with the finite-sum equivalence. -/
theorem sumElim_comp_finSumFinEquiv {k h : ℕ} {A : Type*}
    (ρ : V k → A) (σ : V h → A) :
    Sum.elim ρ σ ∘ finSumFinEquiv.symm = join ρ σ := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [join]

/-- Splitting consequent indices preserves the combined assignment. -/
@[simp] theorem sat_splitFull {n k h : ℕ} (c : Fin n → Bool)
    (ρ : V k → Tree n) (σ : V h → Tree n) (ψ : EConstraint n (k + h)) :
    Core.Full.SatT c (Sum.elim ρ σ) (splitFull ψ) ↔ ESat c (join ρ σ) ψ := by
  simp [Core.Full.SatT, splitFull, sumElim_comp_finSumFinEquiv, ESat]

/-- Public and core full-signature entailment agree over arbitrary trees. -/
theorem existsEntailsAny_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntailsAny c φ ψ ↔
      Core.Full.ExistsEntailsT c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntailsAny, Core.Full.ExistsEntailsT, Core.Full.ExistsEntailsTIn]

/-- Public and core full-signature entailment agree over regular trees. -/
theorem existsEntailsAnyReg_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntailsAnyReg c φ ψ ↔
      Core.Full.ExistsEntailsTReg c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntailsAnyReg, Core.Full.ExistsEntailsTReg]

/-- Public and core full-signature entailment agree over finite trees. -/
theorem existsEntailsAnyFin_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntailsAnyFin c φ ψ ↔
      Core.Full.ExistsEntailsTFin c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntailsAnyFin, Core.Full.ExistsEntailsTFin]

/-- Convert a bottom–constructor literal to the core syntax. -/
def toCoreBF {n k : ℕ} : BFLit n k → Core.Lit n (Fin k)
  | .le x y => .le x y
  | .leF x a => .lef x a
  | .fLe a x => .fle a x
  | .eqBot x => .bot x

/-- Separate the visible and hidden indices of a bottom–constructor consequent. -/
def splitBF {n k h : ℕ} (ψ : BFConstraint n (k + h)) :
    List (Core.Lit n (Fin k ⊕ Fin h)) :=
  ψ.map fun l => (toCoreBF l).map finSumFinEquiv.symm

private theorem holds_toCoreBF {n k : ℕ} (ρ : V k → Tree n) (l : BFLit n k) :
    Core.Full.HoldsT (fun _ => false) ρ (Core.Full.ofLit (toCoreBF l)) ↔
      l.toELit.holds (fun _ => false) ρ := by
  cases l <;> rfl

private theorem ofLit_map {n : ℕ} {A B : Type*} (f : A → B) (l : Core.Lit n A) :
    Core.Full.ofLit (l.map f) = (Core.Full.ofLit l).map f := by
  cases l <;> rfl

private theorem sat_toCoreBF {n k : ℕ} (ρ : V k → Tree n) (φ : BFConstraint n k) :
    Core.Full.SatT (fun _ => false) ρ ((φ.map toCoreBF).map Core.Full.ofLit) ↔
      BFSat ρ φ := by
  simp [Core.Full.SatT, BFSat, ESat, holds_toCoreBF]

private theorem sat_splitBF {n k h : ℕ} (ρ : V k → Tree n) (σ : V h → Tree n)
    (ψ : BFConstraint n (k + h)) :
    Core.Full.SatT (fun _ => false) (Sum.elim ρ σ)
      ((splitBF ψ).map Core.Full.ofLit) ↔ BFSat (join ρ σ) ψ := by
  simp [Core.Full.SatT, splitBF, ofLit_map, sumElim_comp_finSumFinEquiv,
    holds_toCoreBF, BFSat, ESat]

private theorem restricted_range_iff {n : ℕ} {X Z D : Type*} (f : D → Tree n)
    (P : Tree n → Prop) (c : Fin n → Bool)
    (φ : List (Core.Full.LitT n X)) (ψ : List (Core.Full.LitT n (X ⊕ Z))) :
    Core.Full.ExistsEntailsTIn (fun t => P t ∧ ∃ d, f d = t) c φ ψ ↔
      ∀ ρ : X → D, (∀ x, P (f (ρ x))) → Core.Full.SatT c (f ∘ ρ) φ →
        ∃ σ : Z → D, (∀ z, P (f (σ z))) ∧
          Core.Full.SatT c (Sum.elim (f ∘ ρ) (f ∘ σ)) ψ := by
  classical
  constructor
  · intro H ρ hp hs
    obtain ⟨σ, hσ, ht⟩ := H (f ∘ ρ) (fun x => ⟨hp x, ρ x, rfl⟩) hs
    choose τ hτ using fun z => (hσ z).2
    have he : f ∘ τ = σ := funext hτ
    exact ⟨τ, fun z => (hτ z).symm ▸ (hσ z).1, he.symm ▸ ht⟩
  · intro H ρ hp hs
    choose τ hτ using fun x => (hp x).2
    have he : f ∘ τ = ρ := funext hτ
    obtain ⟨σ, hσ, ht⟩ := H τ (fun x => (hτ x).symm ▸ (hp x).1) (he.symm ▸ hs)
    exact ⟨f ∘ σ, fun z => ⟨hσ z, σ z, rfl⟩, he ▸ ht⟩

/-- Public top-free semantics agree with the constructor-set core. -/
theorem existsEntails_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntails φ ψ ↔ Core.ExistsEntails (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntails_topFree_iff]
  simp only [ExistsEntails, Core.Full.ExistsEntailsTopFree, Core.Full.ExistsEntailsTIn,
    sat_toCoreBF, sat_splitBF]
  rfl

/-- The top-free bridge preserves both regular assignments. -/
theorem existsEntailsReg_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsReg φ ψ ↔
      Core.ExistsEntailsIn Core.IsRegularTree (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntailsReg_topFree_iff]
  unfold Core.Full.ExistsEntailsTopFreeReg
  rw [restricted_range_iff]
  simp only [ExistsEntailsReg, sat_toCoreBF, sat_splitBF]
  rfl

/-- The top-free bridge preserves both finite assignments. -/
theorem existsEntailsFin_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsFin φ ψ ↔
      Core.ExistsEntailsIn Core.IsFiniteTree (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntailsFin_topFree_iff]
  unfold Core.Full.ExistsEntailsTopFreeFin
  rw [restricted_range_iff]
  simp only [ExistsEntailsFin, sat_toCoreBF, sat_splitBF]
  rfl

/-- Decide top-free covariant existential entailment over arbitrary trees. -/
@[instance_reducible] def decideExistsEntails {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntails φ ψ) := by
  letI := Core.Main.decideExistsEntails (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntails_iff_core φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntails_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntails φ ψ) = true ↔ ExistsEntails φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntails φ ψ)

/-- Decide top-free covariant existential entailment over regular trees. -/
@[instance_reducible] def decideExistsEntailsReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsReg φ ψ) := by
  letI := Core.Main.decideExistsEntailsReg (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntailsReg_iff_core φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsReg_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsReg φ ψ) = true ↔ ExistsEntailsReg φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg φ ψ)

/-- Decide top-free covariant existential entailment over finite trees. -/
@[instance_reducible] def decideExistsEntailsFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsFin φ ψ) := by
  letI := Core.Main.decideExistsEntailsFin (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntailsFin_iff_core φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsFin_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsFin φ ψ) = true ↔ ExistsEntailsFin φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin φ ψ)

/-- Decide full-signature existential entailment over arbitrary trees. -/
@[instance_reducible] def decideExistsEntailsAny {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntailsAny c φ ψ) := by
  letI := Core.Main.decideExistsEntailsAny c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntailsAny_iff_core c φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntailsAny_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntailsAny c φ ψ) = true ↔ ExistsEntailsAny c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAny c φ ψ)

/-- Decide full-signature existential entailment over regular trees. -/
@[instance_reducible] def decideExistsEntailsAnyReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntailsAnyReg c φ ψ) := by
  letI := Core.Main.decideExistsEntailsAnyReg c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntailsAnyReg_iff_core c φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsAnyReg_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntailsAnyReg c φ ψ) = true ↔ ExistsEntailsAnyReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyReg c φ ψ)

/-- Decide full-signature existential entailment over finite trees. -/
@[instance_reducible] def decideExistsEntailsAnyFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntailsAnyFin c φ ψ) := by
  letI := Core.Main.decideExistsEntailsAnyFin c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntailsAnyFin_iff_core c φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsAnyFin_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntailsAnyFin c φ ψ) = true ↔ ExistsEntailsAnyFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyFin c φ ψ)

end DeciENSSE
