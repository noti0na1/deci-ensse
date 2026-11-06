import DeciENSSE.Core.Full.Basic
import DeciENSSE.Core.Full.Observations
import DeciENSSE.Support.Normalization
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
- `finiteTop_normalize_iff`, `regularTop_normalize_iff`: normalization and
  duality preserve the tree classes
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

/-- Normalization preserves and reflects finite trees (`lem:bg-normalization`(4)),
by the representation of finite trees as trees with a finite domain. -/
theorem finiteTop_normalize_iff (c : Fin n → Bool) (s : Bool) (t : DeciNSSE.Tree n) :
    FiniteTop (DeciNSSE.Tree.normalize c s t) ↔ FiniteTop t := by
  simp only [FiniteTop, Characterization.toTree_range_iff,
    Support.finite_domain_normalize_iff]

/-- Normalization preserves and reflects regular trees (`lem:bg-normalization`(4)),
by the representation of regular trees as trees with finitely many subtrees. -/
theorem regularTop_normalize_iff (c : Fin n → Bool) (s : Bool) (t : DeciNSSE.Tree n) :
    RegularTop (DeciNSSE.Tree.normalize c s t) ↔ RegularTop t := by
  simp only [RegularTop, Characterization.unfold_range_iff,
    Support.finite_subtrees_normalize_iff]

/-- Duality preserves and reflects finite trees (`lem:bg-normalization`(4)). -/
theorem finiteTop_dual_iff (t : DeciNSSE.Tree n) :
    FiniteTop (DeciNSSE.Tree.dual t) ↔ FiniteTop t :=
  finiteTop_normalize_iff _ _ t

/-- Duality preserves and reflects regular trees (`lem:bg-normalization`(4)). -/
theorem regularTop_dual_iff (t : DeciNSSE.Tree n) :
    RegularTop (DeciNSSE.Tree.dual t) ↔ RegularTop t :=
  regularTop_normalize_iff _ _ t

/-- Every jointly realizable finite list of bounds has a finite solution,
provided the underlying covariant constraint system has a finite solution. -/
def FiniteBoundPinning {V : Type*} (χ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop (fun _ => false) χ →
    ∀ B : List (GroundBound n V),
      (∃ ρ, SatT (fun _ => false) ρ χ ∧ ∀ b ∈ B, b.Holds (fun _ => false) ρ) →
      ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ χ ∧
        ∀ b ∈ B, b.Holds (fun _ => false) τ

end DeciENSSE.Core.Full
