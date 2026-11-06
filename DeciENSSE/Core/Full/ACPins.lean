import DeciENSSE.Support.Median
import DeciENSSE.Core.Full.Observations
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Ground bounds for path observations

Finite spine trees translate path observations into upper or lower ground bounds.

## Main declarations

- `ACPins.lower`: the finite spine tree along a path.
- `ACPins.le_dual_iff`: duality reverses a comparison with a finite ground tree
  (`Support.Median.finD`).
- `Observation.bound`, `observation_bound`: the ground bound of an observation.
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace ACPins

/-- Follow one child at each level; each of the other n−1 children is bottom. -/
def lower : List (Fin n) → FTree n → FTree n
  | [], g => g
  | i :: w, g => .node (fun j => if j = i then lower w g else .bot)

/-- A lower spine comparison is equivalent to the endpoint trace comparison. -/
theorem lower_le_iff (w : List (Fin n)) (g : FTree n) (hg : g.toTree ≠ DeciNSSE.Tree.bot)
    (t : DeciNSSE.Tree n) :
    (lower w g).toTree ≤ t ↔ g.toTree ≤ Safety.trace t w := by
  induction w generalizing t with
  | nil => rfl
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [lower, hg]
    · simp [lower]
    · simp only [lower, FTree.toTree_node, DeciNSSE.Tree.node_le_node_iff,
        Safety.trace_cons, Safety.descend_node]
      rw [← ih]
      constructor
      · intro h
        simpa using h i
      · intro h j
        by_cases hj : j = i <;> simp [hj, h]

/-- The constructor with bottom children lies below exactly the nonbottom trees. -/
theorem node_bot_le_iff (t : DeciNSSE.Tree n) :
    DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.bot) ≤ t ↔ t ≠ DeciNSSE.Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;>
    simp [DeciNSSE.Tree.node_le_node_iff]

/-- A constructor endpoint tests membership in the constructor observation. -/
theorem lower_c_iff (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    (lower w (.node (fun _ => .bot))).toTree ≤ t ↔ w ∈ (AC.cobs t).carrier := by
  rw [lower_le_iff w _ (by simp), FTree.toTree_node, FTree.toTree_bot,
    node_bot_le_iff]
  simp only [ne_eq, Safety.trace_eq_bot_iff]
  rfl

/-- A top endpoint tests membership in the top observation. -/
theorem lower_a_iff (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    (lower w .top).toTree ≤ t ↔ AC.aobs t w := by
  rw [lower_le_iff w _ (by simp), FTree.toTree_top, DeciNSSE.Tree.top_le_iff,
    Safety.trace_eq_top_iff]
  rfl

/-- Duality reverses a comparison with a finite ground tree. -/
theorem le_dual_iff (t : DeciNSSE.Tree n) (g : FTree n) :
    t ≤ (Support.Median.finD g).toTree ↔ g.toTree ≤ DeciNSSE.Tree.dual t := by
  rw [Support.Median.finD_toTree, ← DeciNSSE.dual_le_iff, DeciNSSE.dual_involutive]

end ACPins

/-- Translate the observation to a finite ground comparison. -/
def Observation.bound {V : Type*} (o : Observation n V) : GroundBound n V :=
  match o.dual, o.value with
  | false, true => ⟨o.var, true, ACPins.lower o.word (.node (fun _ => .bot))⟩
  | false, false => ⟨o.var, false, Support.Median.finD (ACPins.lower o.word .top)⟩
  | true, true => ⟨o.var, false, Support.Median.finD (ACPins.lower o.word (.node (fun _ => .bot)))⟩
  | true, false => ⟨o.var, true, ACPins.lower o.word .top⟩

/-- The ground comparison holds exactly when the observation does. -/
theorem observation_bound {V : Type*} (ρ : V → DeciNSSE.Tree n) (o : Observation n V) :
    o.bound.Holds (fun _ => false) ρ ↔ o.Holds ρ := by
  classical
  obtain ⟨s,v,w,b⟩ := o
  cases s <;> cases b <;>
    simp only [Observation.bound, GroundBound.Holds, DeciNSSE.treeLe_false_iff_le,
      Observation.Holds,
      Bool.false_eq_true, ite_false, ite_true]
  · rw [ACPins.le_dual_iff, ACPins.lower_a_iff]
    have hh := AC.cobs_dual (DeciNSSE.Tree.dual (ρ v)) w
    simpa only [DeciNSSE.dual_involutive, not_not] using hh.not.symm
  · exact ACPins.lower_c_iff _ _
  · rw [AC.cobs_dual, not_not]
    exact ACPins.lower_a_iff _ _
  · rw [ACPins.le_dual_iff]
    exact ACPins.lower_c_iff _ _

end DeciENSSE.Core.Full
