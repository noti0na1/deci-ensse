import DeciENSSE.Core.Decide
import DeciENSSE.Core.Words.Bound

/-! # Deciding covariant existential entailment over {⊥, fₙ}

The word-layer short-hole theorem supplies the bound for `Core/Decide`.
The resulting procedure decides whether every visible solution extends to
hidden variables over arbitrary covariant trees, including arity zero.

This closes the arbitrary-tree decision proof. `Core/Classes` transfers the
result to regular and finite trees.

## Main declarations

- `decideExistsEntailsTopFree`: the executable decision with the proved bound.
- `decideExistsEntailsTopFree_correct`: its Boolean correctness theorem.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Mortal

variable {n : ℕ} {X Z : Type*}
  [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Executable existential entailment using the proved two-word hole bound. -/
def decideExistsEntailsTopFree (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsTopFree φ ψ) :=
  decideExistsEntailsTopFreeOfShortHoles twoWordHoleBound (shortHoleBound (Fin n)) φ ψ

/-- Boolean correctness of the decision procedure. -/
theorem decideExistsEntailsTopFree_correct (φ : List (Lit n X))
    (ψ : List (Lit n (X ⊕ Z))) :
    @decide (ExistsEntailsTopFree φ ψ) (decideExistsEntailsTopFree φ ψ) = true ↔
      ExistsEntailsTopFree φ ψ :=
  decideExistsEntailsTopFreeOfShortHoles_correct twoWordHoleBound (shortHoleBound (Fin n)) φ ψ

end DeciENSSE.Core
