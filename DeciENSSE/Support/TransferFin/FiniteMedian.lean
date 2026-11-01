import DeciENSSE.Support.Variance.Median
import DeciNSSE.Satisfiability.Cycle


/-! # Finite median realization

Recursion on the sum of three finite heights computes the tree median.
Normalization and duality also preserve finite presentation.

## Main declarations

- `FinT.finD`
- `FinT.fmed`
- `FinT.fmed_toTree`
-/

namespace DeciENSSE.Support.FinT
open DeciNSSE

open DeciNSSE.Tree

variable {n k : ℕ}

/-! ## Finite normalization -/

/-- Finite leaf duality: the finite counterpart of `DeciNSSE.Tree.dual`. -/
def finD (t : FTree n) : FTree n := FTree.normalize (fun _ => false) true t

/-- Finite duality presents tree duality. -/
@[simp] theorem finD_toTree (t : FTree n) : (finD t).toTree = DeciNSSE.Tree.dual t.toTree :=
  FTree.normalize_toTree _ _ _

/-! ## The finite median -/

/-- The root symbol of a finite tree. -/
def rootSym : FTree n → Sym
  | .bot => .bot
  | .top => .top
  | .node _ => .f

/-- The `i`-th child of a node; a leaf is its own child (constant extension). -/
def child : FTree n → Fin n → FTree n
  | .node a, i => a i
  | .bot, _ => .bot
  | .top, _ => .top

/-- The root symbol of bottom is bottom. -/
@[simp] theorem rootSym_bot : rootSym (.bot : FTree n) = .bot := rfl
/-- The root symbol of top is top. -/
@[simp] theorem rootSym_top : rootSym (.top : FTree n) = .top := rfl
/-- The root symbol of a constructor is the constructor label. -/
@[simp] theorem rootSym_node (a : Fin n → FTree n) : rootSym (.node a) = .f := rfl
/-- Descending from bottom retains bottom. -/
@[simp] theorem child_bot (i : Fin n) : child (.bot : FTree n) i = .bot := rfl
/-- Descending from top retains top. -/
@[simp] theorem child_top (i : Fin n) : child (.top : FTree n) i = .top := rfl
/-- Descending from a constructor selects its child. -/
@[simp] theorem child_node (a : Fin n → FTree n) (i : Fin n) : child (.node a) i = a i := rfl

/-- Descending does not increase finite height. -/
theorem height_child_le (t : FTree n) (i : Fin n) : (child t i).height ≤ t.height := by
  cases t with
  | bot => simp
  | top => simp
  | node a => exact (FTree.height_child_lt a i).le

/-- Descending from a constructor strictly decreases finite height. -/
theorem height_child_lt_of_root {t : FTree n} (h : rootSym t = .f) (i : Fin n) :
    (child t i).height < t.height := by
  cases t with
  | bot => simp at h
  | top => simp at h
  | node a => exact FTree.height_child_lt a i

/-- A constructor median needs a constructor input. -/
theorem medianSymN_eq_f {a b c : Sym} (h : medianSymN a b c = .f) :
    a = .f ∨ b = .f ∨ c = .f := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

/-- A constructor median step strictly decreases the sum of the three heights. -/
theorem fmed_decreasing {a b c : FTree n}
    (h : medianSymN (rootSym a) (rootSym b) (rootSym c) = .f) (i : Fin n) :
    (child a i).height + (child b i).height + (child c i).height <
      a.height + b.height + c.height := by
  have ha := height_child_le a i
  have hb := height_child_le b i
  have hc := height_child_le c i
  rcases medianSymN_eq_f h with h | h | h
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega

set_option linter.unusedVariables false in
/-- The median of three finite trees, computed root by root. The hypothesis `h`
is used by the termination proof. -/
def fmed (a b c : FTree n) : FTree n :=
  if h : medianSymN (rootSym a) (rootSym b) (rootSym c) = .f then
    .node fun i => fmed (child a i) (child b i) (child c i)
  else if medianSymN (rootSym a) (rootSym b) (rootSym c) = .bot then .bot else .top
termination_by a.height + b.height + c.height
decreasing_by exact fmed_decreasing h i

/-- A bottom root median produces the finite bottom tree. -/
theorem fmed_of_bot {a b c : FTree n}
    (h : medianSymN (rootSym a) (rootSym b) (rootSym c) = .bot) : fmed a b c = .bot := by
  rw [fmed]; simp [h]

/-- A top root median produces the finite top tree. -/
theorem fmed_of_top {a b c : FTree n}
    (h : medianSymN (rootSym a) (rootSym b) (rootSym c) = .top) : fmed a b c = .top := by
  rw [fmed]; simp [h]

/-- A constructor root median recurses on the three selected children. -/
theorem fmed_of_f {a b c : FTree n}
    (h : medianSymN (rootSym a) (rootSym b) (rootSym c) = .f) :
    fmed a b c = .node fun i => fmed (child a i) (child b i) (child c i) := by
  rw [fmed]; simp [h]

/-- The constant extension at the root equals the finite root symbol. -/
@[simp] theorem extN_toTree_nil (t : FTree n) : extN t.toTree [] = rootSym t := by
  cases t <;> rfl

/-- The constant extension follows the finite child operation. -/
theorem extN_toTree_cons (t : FTree n) (i : Fin n) (w : List (Fin n)) :
    extN t.toTree (i :: w) = extN (child t i).toTree w := by
  cases t <;> simp

/-- The finite median is pointwise on constant extensions. -/
theorem extN_fmed (a b c : FTree n) (w : List (Fin n)) :
    extN (fmed a b c).toTree w =
      medianSymN (extN a.toTree w) (extN b.toTree w) (extN c.toTree w) := by
  induction w generalizing a b c with
  | nil =>
    simp only [extN_toTree_nil]
    cases hm : medianSymN (rootSym a) (rootSym b) (rootSym c)
    · rw [fmed_of_bot hm]; rfl
    · rw [fmed_of_f hm]; rfl
    · rw [fmed_of_top hm]; rfl
  | cons i w ih =>
    have habs : ∀ t : FTree n, rootSym t ≠ .f →
        extN t.toTree (i :: w) = rootSym t := fun t ht => by
      have h := extN_absorb t.toTree [] (i :: w) (by simpa using ht)
      simpa using h
    cases hm : medianSymN (rootSym a) (rootSym b) (rootSym c) with
    | bot =>
      rw [fmed_of_bot hm]
      have h := medianSymN_absorb (rootSym a) (rootSym b) (rootSym c)
        (extN a.toTree (i :: w)) (extN b.toTree (i :: w)) (extN c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | top =>
      rw [fmed_of_top hm]
      have h := medianSymN_absorb (rootSym a) (rootSym b) (rootSym c)
        (extN a.toTree (i :: w)) (extN b.toTree (i :: w)) (extN c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | f =>
      rw [fmed_of_f hm, extN_toTree_cons, child_node, ih, extN_toTree_cons a,
        extN_toTree_cons b, extN_toTree_cons c]

/-- `finite_med`: the median of three finite trees is the finite tree `fmed`. -/
@[simp] theorem fmed_toTree (a b c : FTree n) :
    (fmed a b c).toTree = medN a.toTree b.toTree c.toTree := by
  apply extN_injective
  funext w
  rw [extN_fmed, extN_medN]

end DeciENSSE.Support.FinT
