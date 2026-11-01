import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import DeciENSSE.Core.Full.Observations
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Ground bounds for path observations

Finite spine trees translate path observations into upper or lower ground bounds.

## Main declarations

- `ACPins.lower`
- `ACPins.dual`
- `Observation.bound`
- `observation_bound`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace ACPins

/-- Flip the extreme labels of a finite tree. -/
def dual : FTree n → FTree n
  | .bot => .top
  | .top => .bot
  | .node a => .node (fun i => dual (a i))

/-- Finite label duality presents tree duality. -/
@[simp] theorem dual_toTree (g : FTree n) : (dual g).toTree = DeciNSSE.Tree.dual g.toTree := by
  induction g with
  | bot => simp [dual]
  | top => simp [dual]
  | node a ih => simp [dual, ih]

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
    (lower w (.node (fun _ => .bot))).toTree ≤ t ↔ w ∈ (AC.cobs t).K := by
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
    t ≤ (dual g).toTree ↔ g.toTree ≤ DeciNSSE.Tree.dual t := by
  rw [dual_toTree, ← DeciNSSE.dual_le_iff, DeciNSSE.dual_involutive]

/-- Number of labeled positions, including bottom and top leaves. -/
def size : FTree n → ℕ
  | .bot | .top => 1
  | .node a => 1 + ∑ i, size (a i)

/-- Duality preserves the number of finite-tree positions. -/
theorem size_dual (g : FTree n) : size (dual g) = size g := by
  induction g with
  | bot => rfl
  | top => rfl
  | node a ih => simp [dual, size, ih]

/-- Each spine level adds one constructor and its n−1 sibling leaves. -/
theorem size_lower (w : List (Fin n)) (g : FTree n) :
    size (lower w g) = n * w.length + size g := by
  induction w with
  | nil => simp [lower]
  | cons i w ih =>
    simp [lower, size, apply_ite, Finset.sum_ite, Finset.filter_eq',
      Finset.filter_ne', Finset.card_erase_of_mem, ih, Nat.mul_add]
    have hi := i.isLt
    omega

end ACPins

/-- Translate the observation to a finite ground comparison. -/
def Observation.bound {V : Type*} (o : Observation n V) : GroundBound n V :=
  match o.dual, o.value with
  | false, true => ⟨o.var, true, ACPins.lower o.word (.node (fun _ => .bot))⟩
  | false, false => ⟨o.var, false, ACPins.dual (ACPins.lower o.word .top)⟩
  | true, true => ⟨o.var, false, ACPins.dual (ACPins.lower o.word (.node (fun _ => .bot)))⟩
  | true, false => ⟨o.var, true, ACPins.lower o.word .top⟩

/-- The ground comparison holds exactly when the observation does. -/
theorem observation_bound {V : Type*} (ρ : V → DeciNSSE.Tree n) (o : Observation n V) :
    o.bound.Holds ρ ↔ o.Holds ρ := by
  classical
  obtain ⟨s,v,w,b⟩ := o
  cases s <;> cases b <;>
    simp only [Observation.bound, GroundBound.Holds, Observation.Holds,
      Bool.false_eq_true, ite_false, ite_true]
  · rw [ACPins.le_dual_iff, ACPins.lower_a_iff]
    have hh := AC.cobs_dual (DeciNSSE.Tree.dual (ρ v)) w
    simpa only [DeciNSSE.dual_involutive, not_not] using hh.not.symm
  · exact ACPins.lower_c_iff _ _
  · rw [AC.cobs_dual, not_not]
    exact ACPins.lower_a_iff _ _
  · rw [ACPins.le_dual_iff]
    exact ACPins.lower_c_iff _ _

/-- The observation pin has at most 1 + n(|w|+1) labeled positions. -/
theorem Observation.bound_size {V : Type*} (o : Observation n V) :
    ACPins.size o.bound.tree ≤ 1 + n * (o.word.length + 1) := by
  obtain ⟨s, v, w, b⟩ := o
  cases s <;> cases b <;>
    simp [Observation.bound, ACPins.size_dual, ACPins.size_lower, ACPins.size,
      Nat.mul_add] <;> omega

namespace ACPinsExamples

/-- The third child is selected and both siblings are bottom. -/
theorem ternary_lower : ACPins.lower [2] (.top : FTree 3) =
    .node ![.bot, .bot, .top] := by
  simp only [ACPins.lower]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- There are no sibling fillers at arity one. -/
theorem unary_lower : ACPins.lower [0] (.top : FTree 1) =
    .node (fun _ => .top) := by
  simp only [ACPins.lower]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The two positive observations of a top third child yield valid bounds. -/
theorem ternary_bounds :
    let ρ : Unit → DeciNSSE.Tree 3 := fun _ => DeciNSSE.Tree.node ![DeciNSSE.Tree.bot,
      DeciNSSE.Tree.bot, DeciNSSE.Tree.top]
    (⟨false, (), [2], true⟩ : Observation 3 Unit).bound.Holds ρ ∧
      (⟨true, (), [2], false⟩ : Observation 3 Unit).bound.Holds ρ := by
  simp only [observation_bound]
  exact ObservationExamples.ternary_flags

end ACPinsExamples


end DeciENSSE.Core.Full
