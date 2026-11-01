import DeciENSSE.Core.Mixed.Regular
import DeciENSSE.Support.Nullary
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Finite realization and entailment

Finite bound pinning preserves observations and visible finite values.
Finite entailment reduces to finite satisfiability and arbitrary entailment,
using enumeration of nullary labels for finite satisfiability.

## Main declarations

- `existsEntailsTFin_iff_mixed`: the finite entailment characterization.
- `finite_bound_realization`
- `finite_class_extension`
- `decideExistsEntailsFin`
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

/-- At arity zero, finite satisfiability is enumeration of root labels. -/
theorem satFin_nullary_iff {V : Type*} (c : Fin 0 → Bool) (χ : List (LitT 0 V)) :
    SatFin c χ ↔ ∃ ρ : V → Sym, Nullary.satAnyB ρ χ = true := by
  constructor
  · rintro ⟨ρ, _, hρ⟩
    refine ⟨fun v => Support.Nullary.treeEquiv (ρ v), ?_⟩
    apply (Nullary.satT_ofSym_iff c _ χ).mp
    simpa only [Function.comp_def, Support.Nullary.treeEquiv,
      Equiv.coe_fn_mk, Support.Nullary.ofSym_toSym] using hρ
  · rintro ⟨ρ, hρ⟩
    exact ⟨Support.Nullary.ofSym ∘ ρ,
      fun v => Support.Nullary.toTree_zero_surjective _,
      (Nullary.satT_ofSym_iff c ρ χ).mpr hρ⟩

/-- Executable finite satisfiability at every arity. Constructor sandwiches
require `NeZero n`, so arity zero uses direct label enumeration. -/
def decideSatFin {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) : Decidable (SatFin c χ) := by
  cases n with
  | zero =>
    letI : Fintype Sym := ⟨{Sym.bot, Sym.f, Sym.top}, by intro s; cases s <;> simp⟩
    exact decidable_of_iff _ (satFin_nullary_iff c χ).symm
  | succ m => exact Full.decideSatFin c χ

/-- Finite bound pinning discharges every finite list of observation bounds.
The arity split supplies `NeZero n` for the sandwich translation used by pinning;
every nullary tree already has a finite presentation. -/
theorem finite_bound_realization {V : Type*} (c : Fin n → Bool)
    (χ : List (LitT n V)) (hf : SatFin c χ) : BoundRealization FiniteTop c χ :=
  by
    cases n with
    | zero =>
      intro B hs
      obtain ⟨ρ, hρ, hb⟩ := hs
      exact ⟨ρ, fun v => Support.Nullary.toTree_zero_surjective (ρ v), hρ, hb⟩
    | succ m => exact exists_finite_sat_groundBounds c χ hf

/-- Pin both inequalities of every visible finite tree, obtaining a finite
extension that keeps the visible tuple exactly fixed. -/
theorem finite_class_extension {X Z : Type*} {c : Fin n → Bool} [Fintype X]
    {ψ : List (LitT n (X ⊕ Z))} (hf : SatFin c ψ) :
    ClassExtension FiniteTop c ψ := by
  classical
  intro ρ hρ he
  choose g hg using hρ
  let B : List (GroundBound n (X ⊕ Z)) :=
    Finset.univ.toList.flatMap fun x => [⟨.inl x, true, g x⟩, ⟨.inl x, false, g x⟩]
  obtain ⟨σ, hσ⟩ := he
  have hb : ∀ b ∈ B, b.Holds c (Sum.elim ρ σ) := by
    simp only [B, List.forall_mem_flatMap]
    intro x _
    simp [GroundBound.Holds, hg, DeciNSSE.treeLe_refl]
  obtain ⟨τ, hc, ht, hbτ⟩ := finite_bound_realization c ψ hf B ⟨_, hσ, hb⟩
  have hv (x : X) : τ (.inl x) = ρ x := by
    have hlo := hbτ ⟨.inl x, true, g x⟩ (by simp [B])
    have hhi := hbτ ⟨.inl x, false, g x⟩ (by simp [B])
    change DeciNSSE.Tree.Le c (g x).toTree (τ (.inl x)) at hlo
    change DeciNSSE.Tree.Le c (τ (.inl x)) (g x).toTree at hhi
    rw [hg x] at hlo hhi
    exact DeciNSSE.treeLe_antisymm hhi hlo
  refine ⟨fun z => τ (.inr z), fun z => hc (.inr z), ?_⟩
  have heq : Sum.elim ρ (fun z => τ (.inr z)) = τ := by
    funext v; cases v with
    | inl x => exact (hv x).symm
    | inr z => rfl
  rw [heq]; exact ht

/-- Exact finite dispatch: finite countermodels are obtained from the two
observations, and finite hidden witnesses from pinning the visible tuple. -/
theorem existsEntailsTFin_iff_mixed {X Z : Type*} [Fintype X]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTFin c φ ψ ↔
      ¬ SatFin c φ ∨ (SatFin c ψ ∧ ExistsEntailsT c φ ψ) :=
  fin_dispatch_of_transfer (fun hf => (finite_bound_realization c φ hf).observations)
    (fun hf => finite_class_extension hf)

/-- Computable finite-tree endpoint. -/
def decideExistsEntailsFin {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTFin c φ ψ) := by
  letI := decideSatFin c φ
  letI := decideSatFin c ψ
  letI := decideExistsEntails c φ ψ
  exact decidable_of_iff _ (existsEntailsTFin_iff_mixed c φ ψ).symm

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideSatFin_correct {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) :
    @decide _ (decideSatFin c χ) = true ↔ SatFin c χ :=
  @decide_eq_true_iff _ (decideSatFin c χ)

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideExistsEntailsFin_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsFin c φ ψ) = true ↔ ExistsEntailsTFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin c φ ψ)

end DeciENSSE.Core.Mixed
