import DeciENSSE.Core.Classes
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Core.Nullary

/-! # Existential entailment for every arity

Computable decisions over arbitrary, regular, and finite trees, with explicit
nullary dispatch to finite label enumeration. Positive arities use the general
constraint and word algorithms. No runtime complexity claim is made here.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`:
  covariant bottom–constructor entailment.
- `decideExistsEntailsAny`, `decideExistsEntailsAnyReg`, `decideExistsEntailsAnyFin`:
  the full signature with arbitrary variance.
- `allClassesDeciders`, `decisions`: the three full-signature answers together.
-/

set_option autoImplicit false

namespace DeciENSSE.Core.Main
open Full

variable {n : ℕ} {X Z : Type*}
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Existential entailment over arbitrary trees, including arity zero. -/
def decideExistsEntails (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntails φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntails φ ψ
  | succ _ => exact DeciENSSE.Core.decideExistsEntails φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntails_correct (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide _ (decideExistsEntails φ ψ) = true ↔ ExistsEntails φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntails φ ψ)

/-- Existential entailment over regular trees, including arity zero. -/
def decideExistsEntailsReg (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsRegularTree φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsReg φ ψ
  | succ _ => exact DeciENSSE.Core.decideExistsEntailsReg φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntailsReg_correct (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsReg φ ψ) = true ↔ ExistsEntailsIn IsRegularTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg φ ψ)

/-- Existential entailment over finite trees, including arity zero. -/
def decideExistsEntailsFin (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsFiniteTree φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsFin φ ψ
  | succ _ => exact DeciENSSE.Core.decideExistsEntailsFin φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntailsFin_correct (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsFin φ ψ) = true ↔ ExistsEntailsIn IsFiniteTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin φ ψ)

/-- Existential entailment over arbitrary trees, including arity zero. -/
def decideExistsEntailsAny (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsT c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsAny c φ ψ
  | succ _ => exact Mixed.decideExistsEntailsAny c φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntailsAny_correct (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAny c φ ψ) = true ↔ ExistsEntailsT c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAny c φ ψ)

/-- Existential entailment over regular trees, including arity zero. -/
def decideExistsEntailsAnyReg (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTReg c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsAnyReg c φ ψ
  | succ _ => exact Mixed.decideExistsEntailsAnyReg c φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntailsAnyReg_correct (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyReg c φ ψ) = true ↔ ExistsEntailsTReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyReg c φ ψ)

/-- Existential entailment over finite trees, including arity zero. -/
def decideExistsEntailsAnyFin (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTFin c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsAnyFin c φ ψ
  | succ _ => exact Mixed.decideExistsEntailsAnyFin c φ ψ

/-- The decision returns true exactly when the stated entailment holds. -/
theorem decideExistsEntailsAnyFin_correct (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyFin c φ ψ) = true ↔ ExistsEntailsTFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyFin c φ ψ)

/-- The full-signature theorem in all three tree classes simultaneously. -/
def allClassesDeciders (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsT c φ ψ) × Decidable (ExistsEntailsTReg c φ ψ) ×
      Decidable (ExistsEntailsTFin c φ ψ) :=
  ⟨decideExistsEntailsAny c φ ψ, decideExistsEntailsAnyReg c φ ψ,
    decideExistsEntailsAnyFin c φ ψ⟩

/-- Boolean answers, ordered arbitrary, regular, finite. -/
def decisions (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Bool × Bool × Bool :=
  ⟨@decide _ (decideExistsEntailsAny c φ ψ),
    @decide _ (decideExistsEntailsAnyReg c φ ψ),
    @decide _ (decideExistsEntailsAnyFin c φ ψ)⟩

end DeciENSSE.Core.Main
