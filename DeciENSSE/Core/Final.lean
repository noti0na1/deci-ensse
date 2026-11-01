import DeciENSSE.Core.Decide
import DeciENSSE.Core.Words.Bound

/-! # Unconditional existential entailment over {⊥, fₙ}

The short-hole theorem discharges the bound premise of the executable decision
procedure for arbitrary covariant trees, at every arity including zero.

## Main declarations

- `decideExistsEntails`
- `decideExistsEntails_correct`
- `existsEntails_iff_boundedCheck'`
-/

set_option autoImplicit false

namespace DeciENSSE.Core

variable {n : ℕ} {X Z : Type*}
  [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Executable existential entailment decision, with no bound premise. -/
def decideExistsEntails (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntails φ ψ) :=
  decideExistsEntailsOfShortHoles existsHoleBound (shortHoleBound (Fin n)) φ ψ

/-- Correctness of the explicit bounded Boolean check. -/
theorem existsEntails_iff_boundedCheck' (φ : List (Lit n X))
    (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntails φ ψ ↔ boundedCheck existsHoleBound φ ψ = true :=
  existsEntails_iff_boundedCheck existsHoleBound (shortHoleBound (Fin n)) φ ψ

/-- Boolean correctness of the unconditional decision procedure. -/
theorem decideExistsEntails_correct (φ : List (Lit n X))
    (ψ : List (Lit n (X ⊕ Z))) :
    @decide (ExistsEntails φ ψ) (decideExistsEntails φ ψ) = true ↔
      ExistsEntails φ ψ :=
  decideExistsEntailsOfShortHoles_correct existsHoleBound (shortHoleBound (Fin n)) φ ψ

end DeciENSSE.Core
