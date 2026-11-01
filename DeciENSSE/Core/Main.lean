import DeciENSSE.Core.Classes
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Core.Nullary

/-! # Existential entailment for every arity

The six deciders of the core, over finite types `X` of visible and `Z` of hidden
variables: three for the full signature `{⊥, f, ⊤}` with any variance (the variance proof of
`Core.Mixed`) and three for the covariant signature `{⊥, f}` (the covariant proof of
`Core`), over arbitrary, regular and finite trees.

This module is the arity dispatch. The general deciders are correct at every arity,
including zero. At arity zero every tree is `⊥`, `f()` or `⊤`, and each decider below uses
instead the direct label enumeration of `Core.Nullary`, a small finite search that the
kernel evaluates (`decide +kernel`, as in `DeciENSSE.Examples.Public`); at positive arity it
uses the general decider.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`:
  the full signature with any variance.
- `decideExistsEntailsTopFree`, `decideExistsEntailsTopFreeReg`,
  `decideExistsEntailsTopFreeFin`: the covariant bottom–constructor signature.
-/

namespace DeciENSSE.Core.Main
open Full

variable {n : ℕ} {X Z : Type*}
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Full-signature entailment over arbitrary trees: enumeration at arity zero, the variance
decider `Mixed.decideExistsEntails` otherwise. -/
def decideExistsEntails (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsT c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntails c φ ψ
  | succ _ => exact Mixed.decideExistsEntails c φ ψ

/-- Full-signature entailment over regular trees: enumeration at arity zero,
`Mixed.decideExistsEntailsReg` otherwise. -/
def decideExistsEntailsReg (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTReg c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsReg c φ ψ
  | succ _ => exact Mixed.decideExistsEntailsReg c φ ψ

/-- Full-signature entailment over finite trees: enumeration at arity zero,
`Mixed.decideExistsEntailsFin` otherwise. -/
def decideExistsEntailsFin (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTFin c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsFin c φ ψ
  | succ _ => exact Mixed.decideExistsEntailsFin c φ ψ

/-- Covariant bottom–constructor entailment over arbitrary trees: enumeration at arity zero,
the covariant decider `Core.decideExistsEntailsTopFree` otherwise. -/
def decideExistsEntailsTopFree (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (Core.ExistsEntailsTopFree φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsTopFree φ ψ
  | succ _ => exact Core.decideExistsEntailsTopFree φ ψ

/-- Covariant bottom–constructor entailment over regular trees: enumeration at arity zero,
`Core.decideExistsEntailsTopFreeReg` otherwise. -/
def decideExistsEntailsTopFreeReg (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsRegularTree φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsTopFreeReg φ ψ
  | succ _ => exact Core.decideExistsEntailsTopFreeReg φ ψ

/-- Covariant bottom–constructor entailment over finite trees: enumeration at arity zero,
`Core.decideExistsEntailsTopFreeFin` otherwise. -/
def decideExistsEntailsTopFreeFin (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsFiniteTree φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsTopFreeFin φ ψ
  | succ _ => exact Core.decideExistsEntailsTopFreeFin φ ψ

end DeciENSSE.Core.Main
