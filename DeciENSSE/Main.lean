import Mathlib.Logic.Equiv.Fin.Basic
import DeciENSSE.Core.Main
import DeciENSSE.Semantics
import DeciENSSE.Core.Full.Bridge

/-! # Decidable existential subtype entailment

Existential non-structural subtype entailment `φ ⊨ ∃ z̄. ψ` is decidable for one
constructor `f` of any arity `n ≥ 0`, over arbitrary, regular and finite trees, in two
signatures:
- `{⊥, f, ⊤}` with any variance `c : Fin n → Bool`: `decideExistsEntails`,
  `decideExistsEntailsReg` and `decideExistsEntailsFin` decide `ExistsEntails`,
  `ExistsEntailsReg` and `ExistsEntailsFin`;
- `{⊥, f}` with `f` covariant, over top-free trees: `decideExistsEntailsTopFree`,
  `decideExistsEntailsTopFreeReg` and `decideExistsEntailsTopFreeFin` decide
  `ExistsEntailsTopFree` and its regular and finite variants.

The deciders are computable definitions with no premises. Each `_correct` theorem states
that a decider returns `true` exactly when its entailment holds; it is an instance of
`decide_eq_true_iff`. The substance is the construction of the deciders: they are ordinary
definitions, not `noncomputable` ones, whose answers come from finite searches justified by
the proofs listed below.

## Proof map

Each decider converts its constraints to the core syntax over the visible carrier `Fin k`
and the combined carrier `Fin k ⊕ Fin h` (`toCoreFull`, `splitFull`, `toCoreBF`, `splitBF`
and the `_iff_core` theorems of this module) and calls the arity dispatch `Core.Main`. At
arity zero `Core.Nullary` enumerates root labels. At positive arity the two signatures have
separate proofs.

The full signature, in `Core/Mixed`:
- `Core.Mixed.decideExistsEntails` (`Mixed/Final`) runs the bounded search
  `Core.Mixed.decideExistsEntailsOfShortHoles` (`Mixed/Decide`) with the length bound
  `Core.Words.Self.selfHoleBound`. The search tests satisfiability of both sides,
  condition (I0) and condition (U), and then looks for a short hole in every extracted
  two-word instance with self events.
- It is exact by `Core.Mixed.existsEntailsT_iff_boundedSelf`, which combines
  `Core.Mixed.mixed_reduction` (`Mixed/Extract`: under (I0) and (U), condition (II) fails
  exactly when an extracted instance has a hole) with the three conditions
  `Core.Mixed.three_conditions_mixed` (`Mixed/Conditions`), and with the short-hole theorem
  `Core.Words.Self.shortHoleBoundSelf` (`Words/Self/Bound`).
- The short-hole theorem joins the non-mortal bound
  `Core.Words.Self.nonMortalShortHoleBoundSelf` and the mortal bound
  `Core.Words.Self.mortalShortHoleBoundSelf` (`Words/Self/Mortal`), which rests on anchored
  compression `Anchored.exists_short_posHole_elementary`.
- Regular trees: `Core.Mixed.existsEntailsTReg_iff_mixed` (regular and arbitrary entailment
  agree) gives `Core.Mixed.decideExistsEntailsReg`. Finite trees:
  `Core.Mixed.existsEntailsTFin_iff_mixed` (finite entailment holds iff the antecedent has
  no finite solution, or the consequent has one and arbitrary entailment holds) gives
  `Core.Mixed.decideExistsEntailsFin`.

The covariant signature, in `Core`:
- `Core.decideExistsEntailsTopFree` (`Core/Final`) runs the bounded search
  `Core.decideExistsEntailsTopFreeOfShortHoles` (`Core/Decide`) with the length bound
  `Core.Words.twoWordHoleBound`. It is exact by `Core.existsEntails_iff_bounded`, which
  combines `Core.ss2_reduction` (`Core/Reduction`: under `Core.CondI0` and `Core.CondLive`,
  the closure condition `Core.CondII` fails exactly when an extracted two-word instance has a
  hole) and `Core.three_conditions` (`Core/Horn`) with the short-hole theorem
  `Core.Words.shortHoleBound` (`Words/Bound`), the case of
  `Core.Words.Self.shortHoleBoundSelf` without self events.
- Regular and finite trees: `Core.existsEntailsReg_iff` and `Core.existsEntailsFin_iff`
  give `Core.decideExistsEntailsTopFreeReg` and `Core.decideExistsEntailsTopFreeFin`
  (`Core/Classes`).
- The covariant core describes a tree by its set of constructor positions;
  `Core.Full.existsEntailsIn_bridge` (`Full/Bridge`) identifies these sets with top-free
  trees, which `existsEntailsTopFree_iff_core` uses.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin` and their
  `_correct` theorems: the full signature.
- `decideExistsEntailsTopFree`, `decideExistsEntailsTopFreeReg`,
  `decideExistsEntailsTopFreeFin` and their `_correct` theorems: the covariant signature.
- `toCoreFull`, `splitFull`, `existsEntails_iff_core`, `existsEntailsReg_iff_core`,
  `existsEntailsFin_iff_core`: conversion of the full signature to the core.
- `toCoreBF`, `splitBF`, `existsEntailsTopFree_iff_core`, `existsEntailsTopFreeReg_iff_core`,
  `existsEntailsTopFreeFin_iff_core`: conversion of the covariant signature to the core.
-/

namespace DeciENSSE
open DeciNSSE

/-! ## Conversion of the full signature -/

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
theorem existsEntails_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntails c φ ψ ↔
      Core.Full.ExistsEntailsT c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntails, Core.Full.ExistsEntailsT, Core.Full.ExistsEntailsTIn]

/-- Public and core full-signature entailment agree over regular trees. -/
theorem existsEntailsReg_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntailsReg c φ ψ ↔
      Core.Full.ExistsEntailsTReg c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntailsReg, Core.Full.ExistsEntailsTReg]

/-- Public and core full-signature entailment agree over finite trees. -/
theorem existsEntailsFin_iff_core {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    ExistsEntailsFin c φ ψ ↔
      Core.Full.ExistsEntailsTFin c (φ.map toCoreFull) (splitFull ψ) := by
  simp [ExistsEntailsFin, Core.Full.ExistsEntailsTFin]

/-! ## Conversion of the covariant signature -/

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

/-- Quantifying presentations that satisfy `P` is restricting to the image where `P` holds. -/
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
theorem existsEntailsTopFree_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFree φ ψ ↔ Core.ExistsEntailsTopFree (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntails_topFree_iff]
  simp only [ExistsEntailsTopFree, Core.Full.ExistsEntailsTopFree, Core.Full.ExistsEntailsTIn,
    sat_toCoreBF, sat_splitBF]

/-- The top-free bridge preserves both regular assignments. -/
theorem existsEntailsTopFreeReg_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFreeReg φ ψ ↔
      Core.ExistsEntailsIn Core.IsRegularTree (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntailsReg_topFree_iff]
  unfold Core.Full.ExistsEntailsTopFreeReg
  rw [restricted_range_iff]
  simp only [ExistsEntailsTopFreeReg, sat_toCoreBF, sat_splitBF]

/-- The top-free bridge preserves both finite assignments. -/
theorem existsEntailsTopFreeFin_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFreeFin φ ψ ↔
      Core.ExistsEntailsIn Core.IsFiniteTree (φ.map toCoreBF) (splitBF ψ) := by
  rw [Core.Full.existsEntailsFin_topFree_iff]
  unfold Core.Full.ExistsEntailsTopFreeFin
  rw [restricted_range_iff]
  simp only [ExistsEntailsTopFreeFin, sat_toCoreBF, sat_splitBF]

/-! ## The full signature -/

/-- Decide full-signature existential entailment over arbitrary trees. -/
@[instance_reducible] def decideExistsEntails {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntails c φ ψ) := by
  letI := Core.Main.decideExistsEntails c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntails_iff_core c φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntails_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntails c φ ψ) = true ↔ ExistsEntails c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntails c φ ψ)

/-- Decide full-signature existential entailment over regular trees. -/
@[instance_reducible] def decideExistsEntailsReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntailsReg c φ ψ) := by
  letI := Core.Main.decideExistsEntailsReg c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntailsReg_iff_core c φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsReg_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntailsReg c φ ψ) = true ↔ ExistsEntailsReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg c φ ψ)

/-- Decide full-signature existential entailment over finite trees. -/
@[instance_reducible] def decideExistsEntailsFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) : Decidable (ExistsEntailsFin c φ ψ) := by
  letI := Core.Main.decideExistsEntailsFin c (φ.map toCoreFull) (splitFull ψ)
  exact decidable_of_iff _ (existsEntailsFin_iff_core c φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsFin_correct {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    @decide _ (decideExistsEntailsFin c φ ψ) = true ↔ ExistsEntailsFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin c φ ψ)

/-! ## The covariant signature -/

/-- Decide top-free covariant existential entailment over arbitrary trees. -/
@[instance_reducible] def decideExistsEntailsTopFree {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFree φ ψ) := by
  letI := Core.Main.decideExistsEntailsTopFree (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntailsTopFree_iff_core φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntailsTopFree_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFree φ ψ) = true ↔ ExistsEntailsTopFree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFree φ ψ)

/-- Decide top-free covariant existential entailment over regular trees. -/
@[instance_reducible] def decideExistsEntailsTopFreeReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeReg φ ψ) := by
  letI := Core.Main.decideExistsEntailsTopFreeReg (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntailsTopFreeReg_iff_core φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsTopFreeReg_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFreeReg φ ψ) = true ↔ ExistsEntailsTopFreeReg φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFreeReg φ ψ)

/-- Decide top-free covariant existential entailment over finite trees. -/
@[instance_reducible] def decideExistsEntailsTopFreeFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeFin φ ψ) := by
  letI := Core.Main.decideExistsEntailsTopFreeFin (φ.map toCoreBF) (splitBF ψ)
  exact decidable_of_iff _ (existsEntailsTopFreeFin_iff_core φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsTopFreeFin_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFreeFin φ ψ) = true ↔ ExistsEntailsTopFreeFin φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFreeFin φ ψ)

end DeciENSSE
