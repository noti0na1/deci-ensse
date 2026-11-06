import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Core.Nullary

/-! # Existential entailment for every arity

The three deciders of the core, for the signature `{⊥, f, ⊤}` with any variance, over finite
types `X` of visible and `Z` of hidden variables, over arbitrary, regular and finite trees.
The deciders for `{⊥, f}` in `DeciENSSE.Main` call them after the top-freeness gadget.

This module is the arity dispatch. The general deciders of `Core.Mixed` are correct at every
arity, including zero. At arity zero every tree is `⊥`, `f()` or `⊤`, and each decider below
uses instead the direct label enumeration of `Core.Nullary`, a small finite search that the
kernel evaluates (`decide +kernel`, as in `DeciENSSE.Examples.Public`); at positive arity it
uses the general decider.

## Main declarations

- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`.
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

end DeciENSSE.Core.Main
