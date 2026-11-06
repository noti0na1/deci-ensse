import DeciENSSE.Core.Full.Basic
import DeciENSSE.Support.Nullary

/-! # Existential entailment at arity zero

At arity zero a tree is determined by its root label `⊥`, `f()` or `⊤`. Every such tree is
finite and regular, so the three tree classes coincide, and existential entailment reduces to
an enumeration of the root labels of the visible and the hidden variables. `Core.Main` uses
these deciders at arity zero, also for the signature `{⊥, f}` after the top-freeness gadget
(`DeciENSSE.TopFree`).

## Main declarations

- `satAnyB`, `existsEntailsT_iff_labels`, `entailsAnyB`: literals on root labels, and the
  enumeration.
- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`: the three tree
  classes.
-/

namespace DeciENSSE.Core.Nullary
open DeciNSSE DeciENSSE.Core.Full
open DeciENSSE.Support.Nullary (ofSym ofSym_bot ofSym_top treeLe_zero_iff treeEquiv
  unfold_zero_surjective toTree_zero_surjective)

variable {V X Z : Type*}

private theorem comp_sumElim {A B D E : Type*} (f : D → E)
    (ρ : A → D) (σ : B → D) :
    f ∘ Sum.elim ρ σ = Sum.elim (f ∘ ρ) (f ∘ σ) := by
  funext v
  cases v <;> rfl

/-- Surjective presentations preserve both quantifiers of existential entailment. -/
private theorem presentation_iff {A D : Type*} (e : A → D)
    (he : Function.Surjective e) (P : (X → D) → Prop) (Q : (X ⊕ Z → D) → Prop) :
    (∀ ρ, P ρ → ∃ σ, Q (Sum.elim ρ σ)) ↔
      ∀ ρ : X → A, P (e ∘ ρ) → ∃ σ : Z → A, Q (e ∘ Sum.elim ρ σ) := by
  classical
  constructor
  · intro h ρ hρ
    obtain ⟨σ, hσ⟩ := h (e ∘ ρ) hρ
    choose τ hτ using fun z => he (σ z)
    refine ⟨τ, ?_⟩
    simpa only [comp_sumElim, show e ∘ τ = σ from funext hτ] using hσ
  · intro h ρ hρ
    choose τ hτ using fun x => he (ρ x)
    have ht : e ∘ τ = ρ := funext hτ
    obtain ⟨σ, hσ⟩ := h τ (ht.symm ▸ hρ)
    exact ⟨e ∘ σ, by simpa only [comp_sumElim, ht] using hσ⟩

/-! ## Three root labels

At arity zero the variance is the empty function, so it plays no role. -/

local instance : Fintype Sym where
  elems := {Sym.bot, Sym.f, Sym.top}
  complete s := by cases s <;> simp

/-- Evaluate a full literal on root labels; the empty child tuple disappears. -/
def holdsAnyB (ρ : V → Sym) : LitT 0 V → Bool
  | .le u v => decide (ρ u ≤ ρ v)
  | .fle _ u => decide (Sym.f ≤ ρ u)
  | .lef u _ => decide (ρ u ≤ Sym.f)
  | .bot u => decide (ρ u = Sym.bot)
  | .top u => decide (ρ u = Sym.top)

/-- Check every full-signature literal on root labels. -/
def satAnyB (ρ : V → Sym) (χ : List (LitT 0 V)) : Bool := χ.all (holdsAnyB ρ)

/-- Full-signature evaluation agrees with tree satisfaction. -/
theorem holdsT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Sym) (l : LitT 0 V) :
    HoldsT c (ofSym ∘ ρ) l ↔ holdsAnyB ρ l = true := by
  cases l <;>
    simp [HoldsT, holdsAnyB, Function.comp_def, treeLe_zero_iff, ← ofSym_bot, ← ofSym_top]

/-- Full-signature conjunction evaluation agrees with satisfaction. -/
theorem satT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Sym) (χ : List (LitT 0 V)) :
    SatT c (ofSym ∘ ρ) χ ↔ satAnyB ρ χ = true := by
  simp only [SatT, satAnyB, List.all_eq_true, holdsT_ofSym_iff]

/-- Full-signature entailment reduces to finite label valuations. -/
theorem existsEntailsT_iff_labels (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔
      ∀ ρ : X → Sym, satAnyB ρ φ = true →
        ∃ σ : Z → Sym, satAnyB (Sum.elim ρ σ) ψ = true := by
  simp only [ExistsEntailsT, ExistsEntailsTIn, implies_true, forall_const, true_and]
  rw [presentation_iff ofSym treeEquiv.symm.surjective
    (fun ρ => SatT c ρ φ) (fun ρ => SatT c ρ ψ)]
  simp only [satT_ofSym_iff]

/-- A class containing every nullary tree imposes no restriction. -/
theorem existsEntailsTIn_iff (C : Tree 0 → Prop) (hC : ∀ t, C t)
    (c : Fin 0 → Bool) (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTIn C c φ ψ ↔ ExistsEntailsT c φ ψ := by
  simp [ExistsEntailsTIn, ExistsEntailsT, hC]

/-- Every nullary tree has a regular presentation. -/
theorem existsEntailsTReg_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ :=
  (Full.existsEntailsTReg_iff c φ ψ).trans
    (existsEntailsTIn_iff _ unfold_zero_surjective c φ ψ)

/-- Every nullary tree has a finite presentation. -/
theorem existsEntailsTFin_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTFin c φ ψ ↔ ExistsEntailsT c φ ψ :=
  (Full.existsEntailsTFin_iff c φ ψ).trans
    (existsEntailsTIn_iff _ toTree_zero_surjective c φ ψ)

section Deciders
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Enumerate visible and hidden root-label valuations. -/
def entailsAnyB (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Bool :=
  decide (∀ ρ : X → Sym, satAnyB ρ φ = true →
    ∃ σ : Z → Sym, satAnyB (Sum.elim ρ σ) ψ = true)

/-- Label enumeration decides full-signature entailment. -/
theorem entailsAnyB_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    entailsAnyB φ ψ = true ↔ ExistsEntailsT c φ ψ := by
  simpa only [entailsAnyB, decide_eq_true_eq] using (existsEntailsT_iff_labels c φ ψ).symm

/-- Decide full-signature entailment at arity zero by label enumeration. -/
def decideExistsEntails (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsT c φ ψ) :=
  decidable_of_iff _ (entailsAnyB_iff c φ ψ)

/-- Decide full-signature regular-tree entailment at arity zero by label enumeration. -/
def decideExistsEntailsReg (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsTReg c φ ψ) :=
  decidable_of_iff _ ((entailsAnyB_iff c φ ψ).trans (existsEntailsTReg_iff c φ ψ).symm)

/-- Decide full-signature finite-tree entailment at arity zero by label enumeration. -/
def decideExistsEntailsFin (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsTFin c φ ψ) :=
  decidable_of_iff _ ((entailsAnyB_iff c φ ψ).trans (existsEntailsTFin_iff c φ ψ).symm)

/-- Every decision procedure for this proposition gives the same Boolean answer. -/
theorem decideExistsEntails_agrees (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z)))
    (d : Decidable (ExistsEntailsT c φ ψ)) :
    @decide _ (decideExistsEntails c φ ψ) = @decide _ d := by
  congr 1

end Deciders

end DeciENSSE.Core.Nullary
