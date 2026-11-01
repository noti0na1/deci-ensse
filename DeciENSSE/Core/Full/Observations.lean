import DeciENSSE.Core.Full.AC
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Tree

/-! # Finite observations and ground bounds

A signed path observation records membership in one of the two tree observations.
Ground bounds compare a variable with a finite tree.

## Main declarations

- `Observation`
- `Observation.Holds`
- `GroundBound`
- `GroundBound.Holds`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

/-- `dual = false` observes C; `dual = true` observes the complement of A.
The `value` field chooses the observation or its negation. -/
structure Observation (n : ℕ) (X : Type*) where
  dual : Bool
  var : X
  word : List (Fin n)
  value : Bool

/-- Interpret the observation on a tree assignment. -/
def Observation.Holds {X : Type*} (ρ : X → DeciNSSE.Tree n) (o : Observation n X) : Prop :=
  let t := if o.dual then DeciNSSE.Tree.dual (ρ o.var) else ρ o.var
  if o.value then o.word ∈ (AC.cobs t).K else o.word ∉ (AC.cobs t).K

/-- A finite lower or upper bound on one variable. -/
structure GroundBound (n : ℕ) (V : Type*) where
  var : V
  lower : Bool
  tree : FTree n

/-- Interpret the finite ground comparison in covariant tree order. -/
def GroundBound.Holds {V : Type*} (ρ : V → DeciNSSE.Tree n) (b : GroundBound n V) : Prop :=
  if b.lower then b.tree.toTree ≤ ρ b.var else ρ b.var ≤ b.tree.toTree

namespace ObservationExamples

/-- At child two, top has C and A; the dual-C observation is therefore false. -/
theorem ternary_flags :
    let ρ : Unit → DeciNSSE.Tree 3 := fun _ => DeciNSSE.Tree.node ![DeciNSSE.Tree.bot,
      DeciNSSE.Tree.bot, DeciNSSE.Tree.top]
    (⟨false, (), [2], true⟩ : Observation 3 Unit).Holds ρ ∧
      (⟨true, (), [2], false⟩ : Observation 3 Unit).Holds ρ := by
  simp [Observation.Holds]

/-- Both directions of a ground bound can pin the same finite tree. -/
theorem ground_bounds_nonvacuous (g : FTree n) :
    (⟨(), true, g⟩ : GroundBound n Unit).Holds (fun _ => g.toTree) ∧
      (⟨(), false, g⟩ : GroundBound n Unit).Holds (fun _ => g.toTree) :=
  ⟨le_rfl, le_rfl⟩

end ObservationExamples


end DeciENSSE.Core.Full
