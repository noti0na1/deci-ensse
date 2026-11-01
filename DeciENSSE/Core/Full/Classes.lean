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
- `SatisfiableTopIn`
- `FiniteBoundPinning`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

/-- Trees presented by a finite graph. -/
def RegularTop (t : DeciNSSE.Tree n) : Prop := ∃ g : RGraph n, g.unfold = t
/-- Trees presented by a finite term. -/
def FiniteTop (t : DeciNSSE.Tree n) : Prop := ∃ g : FTree n, g.toTree = t

/-- A covariant solution whose values belong to the specified tree class. -/
def SatisfiableTopIn {V : Type*} (C : DeciNSSE.Tree n → Prop) (χ : List (LitT n V)) : Prop :=
  ∃ ρ, (∀ v, C (ρ v)) ∧ SatT (fun _ => false) ρ χ

/-- Every jointly realizable finite list of bounds has a finite solution,
provided the underlying covariant constraint system has a finite solution. -/
def FiniteBoundPinning {V : Type*} (χ : List (LitT n V)) : Prop :=
  SatisfiableTopIn FiniteTop χ →
    ∀ B : List (GroundBound n V),
      (∃ ρ, SatT (fun _ => false) ρ χ ∧ ∀ b ∈ B, b.Holds ρ) →
      ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ χ ∧
        ∀ b ∈ B, b.Holds τ

namespace TopExamples

/-- Top has a finite presentation. -/
theorem finite_top : FiniteTop (DeciNSSE.Tree.top : DeciNSSE.Tree n) := ⟨FTree.top, rfl⟩

/-- Top has a regular presentation. -/
theorem regular_top : RegularTop (DeciNSSE.Tree.top : DeciNSSE.Tree n) := by
  apply (Characterization.unfold_range_iff _).mpr
  exact Characterization.subtrees_finite_of_domain_finite _
    (Characterization.domain_toTree_finite FTree.top)

/-- a satisfiable ternary system meets the exact finite pinning premise. -/
theorem finite_pinning_nonvacuous :
    SatisfiableTopIn FiniteTop ([.top ()] : List (LitT 3 Unit)) ∧
      FiniteBoundPinning ([.top ()] : List (LitT 3 Unit)) := by
  constructor
  · exact ⟨fun _ => DeciNSSE.Tree.top, fun _ => finite_top, by simp [SatT, HoldsT]⟩
  · rintro _ B ⟨ρ, hs, hb⟩
    refine ⟨ρ, ?_, hs, hb⟩
    intro v
    cases v
    have ht : ρ () = DeciNSSE.Tree.top := hs (.top ()) (by simp)
    rw [ht]
    exact finite_top

/-- The same ternary antecedent has a regular witness. -/
theorem regular_satisfiable :
    SatisfiableTopIn RegularTop ([.top ()] : List (LitT 3 Unit)) :=
  ⟨fun _ => DeciNSSE.Tree.top, fun _ => regular_top, by simp [SatT, HoldsT]⟩

end TopExamples


end DeciENSSE.Core.Full
