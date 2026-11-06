import DeciENSSE.Core.Full.AC
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Tree

/-! # Finite observations and ground bounds

An observation asserts or denies membership of a path in the nonbottom set C
or the complement of the top leaf cone A. Ground bounds compare a variable with
a finite tree in the specified variance order; covariance is `fun _ => false`.

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
  if o.value then o.word ∈ (AC.cobs t).carrier else o.word ∉ (AC.cobs t).carrier

/-- A finite lower or upper bound on one variable. -/
structure GroundBound (n : ℕ) (V : Type*) where
  var : V
  lower : Bool
  tree : FTree n

/-- Interpret the finite ground comparison in the specified variance order. -/
def GroundBound.Holds {V : Type*} (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n)
    (b : GroundBound n V) : Prop :=
  if b.lower then Tree.Le c b.tree.toTree (ρ b.var)
  else Tree.Le c (ρ b.var) b.tree.toTree

end DeciENSSE.Core.Full
