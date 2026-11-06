import Mathlib.Logic.Equiv.Fin.Basic
import DeciENSSE.Core.Main
import DeciENSSE.Semantics
import DeciENSSE.TopFree

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

Each decider converts its constraints to the core syntax and calls the arity dispatch
`Core.Main`, which enumerates root labels at arity zero (`Core.Nullary`) and runs the
variance proof of `Core/Mixed` at positive arity. Both signatures use this one proof.

The full signature: the visible carrier is `Fin k` and the combined carrier `Fin k ⊕ Fin h`
(`toCoreFull`, `splitFull`, `existsEntails_iff_core` and its two variants).
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

The signature `{⊥, f}` reduces to the full signature at the covariant variance by the
top-freeness gadget of `DeciENSSE.TopFree`:
- `toCoreTopFree` and `splitTopFree` embed the literals (`BFLit.toELit`) and add
  `v ≤ y_v ∧ y_v ≤ f(y_v, …, y_v)` for every visible and every hidden variable `v`, over the
  carriers `Fin k ⊕ Fin k` and `Fin h ⊕ Fin h`.
- `TopFree.existsEntailsTIn_iff_gadget` proves the reduction in every tree class whose
  top-free trees have gadget witnesses (`TopFree.HasWitnesses`): `Ω` over arbitrary and
  regular trees, the full finite tree `T_{h(t)+1}` over finite trees.
- `existsEntailsTopFree_iff_core` and its two variants instantiate it; the three deciders for
  `{⊥, f}` are the full-signature deciders of `Core.Main` on the translated systems, and
  `existsEntailsTopFreeReg_iff` carries `Core.Mixed.existsEntailsTReg_iff_mixed` over to
  `{⊥, f}`.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin` and their
  `_correct` theorems: the full signature.
- `decideExistsEntailsTopFree`, `decideExistsEntailsTopFreeReg`,
  `decideExistsEntailsTopFreeFin` and their `_correct` theorems: the covariant signature.
- `toCoreFull`, `splitFull`, `existsEntails_iff_core`, `existsEntailsReg_iff_core`,
  `existsEntailsFin_iff_core`: conversion of the full signature to the core.
- `toCoreTopFree`, `splitTopFree`, `existsEntailsTopFree_iff_core`,
  `existsEntailsTopFreeReg_iff_core`, `existsEntailsTopFreeFin_iff_core`: conversion of the
  covariant signature to the full-signature core, through the gadget.
- `existsEntailsTopFreeReg_iff`: over `{⊥, f}`, regular and arbitrary entailment agree.
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

/-! ## Conversion of the covariant signature

A bottom–constructor literal is a full-signature literal (`BFLit.toELit`), and covariant
satisfaction is full-signature satisfaction at the covariant variance. The top-freeness gadget
of `DeciENSSE.TopFree` adds `v ≤ y_v ∧ y_v ≤ f(y_v, …, y_v)` for every visible and every
hidden variable `v`; the visible carrier becomes `Fin k ⊕ Fin k` and the hidden one
`Fin h ⊕ Fin h`, the right copies holding the variables `y_v`. -/

/-- A bottom–constructor antecedent in the core syntax, with the gadget on every visible
variable. -/
def toCoreTopFree {n k : ℕ} (φ : BFConstraint n k) :
    List (Core.Full.LitT n (Fin k ⊕ Fin k)) :=
  TopFree.gadgetAnte (List.finRange k) ((φ.map BFLit.toELit).map toCoreFull)

/-- A bottom–constructor consequent in the core syntax, with split indices and the gadget on
every hidden variable. -/
def splitTopFree {n k h : ℕ} (ψ : BFConstraint n (k + h)) :
    List (Core.Full.LitT n ((Fin k ⊕ Fin k) ⊕ (Fin h ⊕ Fin h))) :=
  TopFree.gadgetCons (List.finRange h) (splitFull (ψ.map BFLit.toELit))

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

/-- Public top-free entailment is full-signature entailment after the gadget, over arbitrary
trees. -/
theorem existsEntailsTopFree_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFree φ ψ ↔
      Core.Full.ExistsEntailsT (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ) := by
  rw [toCoreTopFree, splitTopFree,
    ← TopFree.existsEntailsT_iff_gadget List.mem_finRange List.mem_finRange]
  simp only [ExistsEntailsTopFree, Core.Full.ExistsEntailsTIn, BFSat, sat_toCoreFull,
    sat_splitFull]

/-- Public top-free entailment is full-signature entailment after the gadget, over regular
trees. -/
theorem existsEntailsTopFreeReg_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFreeReg φ ψ ↔
      Core.Full.ExistsEntailsTReg (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ) := by
  rw [toCoreTopFree, splitTopFree,
    ← TopFree.existsEntailsTReg_iff_gadget List.mem_finRange List.mem_finRange,
    restricted_range_iff]
  simp only [ExistsEntailsTopFreeReg, BFSat, sat_toCoreFull, sat_splitFull]

/-- Public top-free entailment is full-signature entailment after the gadget, over finite
trees. -/
theorem existsEntailsTopFreeFin_iff_core {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFreeFin φ ψ ↔
      Core.Full.ExistsEntailsTFin (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ) := by
  rw [toCoreTopFree, splitTopFree,
    ← TopFree.existsEntailsTFin_iff_gadget List.mem_finRange List.mem_finRange,
    restricted_range_iff]
  simp only [ExistsEntailsTopFreeFin, BFSat, sat_toCoreFull, sat_splitFull]

/-- Over `{⊥, f}`, as over `{⊥, f, ⊤}`, regular and arbitrary entailment agree: the gadget
reduces both to the full signature, where `Core.Mixed.existsEntailsTReg_iff_mixed` applies. -/
theorem existsEntailsTopFreeReg_iff {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    ExistsEntailsTopFreeReg φ ψ ↔ ExistsEntailsTopFree φ ψ := by
  rw [existsEntailsTopFreeReg_iff_core, existsEntailsTopFree_iff_core]
  exact Core.Mixed.existsEntailsTReg_iff_mixed _ _ _

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
  letI := Core.Main.decideExistsEntails (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)
  exact decidable_of_iff _ (existsEntailsTopFree_iff_core φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntailsTopFree_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFree φ ψ) = true ↔ ExistsEntailsTopFree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFree φ ψ)

/-- Decide top-free covariant existential entailment over regular trees. -/
@[instance_reducible] def decideExistsEntailsTopFreeReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeReg φ ψ) := by
  letI := Core.Main.decideExistsEntailsReg (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)
  exact decidable_of_iff _ (existsEntailsTopFreeReg_iff_core φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsTopFreeReg_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFreeReg φ ψ) = true ↔ ExistsEntailsTopFreeReg φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFreeReg φ ψ)

/-- Decide top-free covariant existential entailment over finite trees. -/
@[instance_reducible] def decideExistsEntailsTopFreeFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeFin φ ψ) := by
  letI := Core.Main.decideExistsEntailsFin (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)
  exact decidable_of_iff _ (existsEntailsTopFreeFin_iff_core φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsTopFreeFin_correct {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) :
    @decide _ (decideExistsEntailsTopFreeFin φ ψ) = true ↔ ExistsEntailsTopFreeFin φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTopFreeFin φ ψ)

end DeciENSSE
