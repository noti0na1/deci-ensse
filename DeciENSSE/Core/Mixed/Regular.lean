import DeciENSSE.Core.Mixed.ClassTransfer
import DeciENSSE.Core.Full.TopGraphs
import DeciENSSE.Core.Mixed.Final
import DeciENSSE.Core.Mixed.FinitePinning
import DeciENSSE.Support.Nullary
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

- `existsEntailsTReg_iff_mixed`: regular and arbitrary entailment coincide.
- `regular_bound_realization`
- `regular_class_extension`
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

/-- Regular satisfiability at every arity. Constructor sandwiches require
`NeZero n`; nullary trees already have regular presentations. -/
theorem satisfiable_regular {V : Type*} [Fintype V] (c : Fin n → Bool)
    {χ : List (LitT n V)} (h : ∃ ρ, SatT c ρ χ) : SatisfiableIn RegularTop c χ := by
  cases n with
  | zero =>
    obtain ⟨ρ, hρ⟩ := h
    exact ⟨ρ, fun v => Support.Nullary.unfold_zero_surjective (ρ v), hρ⟩
  | succ m => exact Full.satisfiable_regular c h

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
  let bindings : List (TopGraphs.Binding V (Fin B.length)) :=
    (List.finRange B.length).map (fun i => ((B.get i).var, i, (B.get i).lower))
  have hb (ρ : V → DeciNSSE.Tree n) (i : Fin B.length) :
      TopGraphs.bindingHolds c g ρ ((B.get i).var, i, (B.get i).lower) ↔
        (B.get i).Holds c ρ := by
    simp only [TopGraphs.bindingHolds, hg, GroundBound.Holds]
  obtain ⟨ρ, hρ, hB⟩ := hs
  obtain ⟨τ, hc, ht, hτ⟩ := TopGraphs.regularize c χ g bindings ⟨ρ, hρ, by
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
  let B : List (TopGraphs.Binding (X ⊕ Z) X) :=
    Finset.univ.toList.flatMap fun x => [(.inl x, x, true), (.inl x, x, false)]
  obtain ⟨σ, hσ⟩ := he
  have hb : ∀ b ∈ B, TopGraphs.bindingHolds c g (Sum.elim ρ σ) b := by
    simp only [B, List.forall_mem_flatMap]
    intro x _
    simp [TopGraphs.bindingHolds, hg, DeciNSSE.treeLe_refl]
  obtain ⟨τ, hc, ht, hbτ⟩ := TopGraphs.regularize c ψ g B ⟨_, hσ, hb⟩
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

/-- Computable regular-tree endpoint, for arbitrary constructor variance. -/
def decideExistsEntailsReg {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTReg c φ ψ) := by
  letI := decideExistsEntails c φ ψ
  exact decidable_of_iff _ (existsEntailsTReg_iff_mixed c φ ψ).symm

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideExistsEntailsReg_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsReg c φ ψ) = true ↔ ExistsEntailsTReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg c φ ψ)

end DeciENSSE.Core.Mixed
