import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Core.Words.Self.Bound
import DeciENSSE.Core.Nullary

/-! # Mixed existential entailment over arbitrary trees

The uniform bound for holes with self events gives a computable entailment
decider over arbitrary trees, at every arity and variance.

## Main declarations

- `decideExistsEntails`,
  `existsEntails_iff_boundedCheck`, `decideExistsEntails_correct`,
  `decideExistsEntails_nullary_agrees`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A computable decision procedure for every arity and variance. -/
def decideExistsEntails (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Decidable (ExistsEntailsT c φ ψ) :=
  decideExistsEntailsOfShortHoles selfHoleBound (shortHoleBoundSelf (Fin n)) c φ ψ

/-- The bounded check is equivalent to existential entailment. -/
theorem existsEntails_iff_boundedCheck (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ boundedCheckMixed selfHoleBound c φ ψ = true :=
  existsEntails_iff_boundedCheckMixed selfHoleBound (shortHoleBoundSelf (Fin n)) c φ ψ

/-- The decision returns true exactly for existential entailment. -/
theorem decideExistsEntails_correct (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide (ExistsEntailsT c φ ψ) (decideExistsEntails c φ ψ) = true ↔
      ExistsEntailsT c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntails c φ ψ)

/-- The general mixed endpoint agrees with the specialized nullary enumeration. -/
theorem decideExistsEntails_nullary_agrees (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntails c φ ψ) =
      @decide _ (Nullary.decideExistsEntails c φ ψ) :=
  (Nullary.decideExistsEntails_agrees c φ ψ (decideExistsEntails c φ ψ)).symm

end DeciENSSE.Core.Mixed
