import DeciENSSE.Core.Full.Basic
import DeciENSSE.Core.Full.Observations
import DeciNSSE.Semantics.Characterization
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Tree

/-! # Regular and finite tree classes

Finite terms and finite graphs present the two restricted tree classes. Ground
bound pinning asks for a finite solution preserving a finite list of comparisons.

## Main declarations

- `RegularTop`
- `FiniteTop`
- `SatisfiableIn`
- `FiniteBoundPinning`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

/-- Trees presented by a finite graph. -/
def RegularTop (t : DeciNSSE.Tree n) : Prop := ∃ g : RGraph n, g.unfold = t
/-- Trees presented by a finite term. -/
def FiniteTop (t : DeciNSSE.Tree n) : Prop := ∃ g : FTree n, g.toTree = t

/-- Every jointly realizable finite list of bounds has a finite solution,
provided the underlying covariant constraint system has a finite solution. -/
def FiniteBoundPinning {V : Type*} (χ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop (fun _ => false) χ →
    ∀ B : List (GroundBound n V),
      (∃ ρ, SatT (fun _ => false) ρ χ ∧ ∀ b ∈ B, b.Holds (fun _ => false) ρ) →
      ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ χ ∧
        ∀ b ∈ B, b.Holds (fun _ => false) τ

end DeciENSSE.Core.Full
