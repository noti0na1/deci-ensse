import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.LeastShape
import DeciNSSE.Satisfiability.Cycle

/-! # Tree medians and finite realization

Constant leaf extensions embed tree order into pointwise label order. Pruning
the pointwise median gives a tree and preserves constructors and duality.

Recursion on the sum of three finite heights computes the tree median.
Normalization and duality also preserve finite presentation.

## Main declarations

- `ext`
- `treeMedian`
- `ext_treeMedian`
- `treeMedian_mono`
- `treeMedian_node`
- `d_treeMedian`
- `Median.finD`
- `Median.finiteMedian`
- `Median.finiteMedian_toTree`
-/

namespace DeciENSSE.Support.Median
open DeciNSSE

open DeciNSSE.Tree

variable {n : ℕ}

/-! ## Constant leaf extension -/

/-- Read the root of the leaf-freezing trace: the label at `w`, or the first leaf
above `w` when `w` leaves the domain. -/
def ext (t : DeciNSSE.Tree n) (w : List (Fin n)) : Sym :=
  ((Safety.trace t w).fn []).getD .f

/-- The constant leaf extension of bottom is bottom at every path. -/
@[simp] theorem ext_bot (w : List (Fin n)) : ext DeciNSSE.Tree.bot w = .bot := by simp [ext]
/-- The constant leaf extension of top is top at every path. -/
@[simp] theorem ext_top (w : List (Fin n)) : ext DeciNSSE.Tree.top w = .top := by simp [ext]
/-- A constructor has constructor label at the empty path. -/
@[simp] theorem ext_node_nil (a : Fin n → DeciNSSE.Tree n) : ext (DeciNSSE.Tree.node a) [] = .f :=
  rfl
/-- The extension of a constructor follows the selected child. -/
@[simp] theorem ext_node_cons (a : Fin n → DeciNSSE.Tree n) (i : Fin n) (w : List (Fin n)) :
    ext (DeciNSSE.Tree.node a) (i :: w) = ext (a i) w := by
  simp [ext]

/-- At a present position the constant extension agrees with the tree label. -/
theorem ext_of_fn {t : DeciNSSE.Tree n} {w : List (Fin n)} {s : Sym}
    (h : t.fn w = some s) : ext t w = s := by
  induction w generalizing t with
  | nil => simp [ext, h]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp at h
    · simp at h
    · rw [ext_node_cons]; exact ih (by simpa using h)

/-- One trace step uses the next label or retains the preceding extreme label. -/
theorem ext_step (t : DeciNSSE.Tree n) (w : List (Fin n)) (i : Fin n) :
    ext t (w ++ [i]) = (t.fn (w ++ [i])).getD (ext t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simp [ext]
  | cons j w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simpa using ih (t := a j)

/-- A top prefix is equivalent to a top label in the constant extension. -/
@[simp] theorem covPrefTop_iff_ext (w : List (Fin n)) (t : DeciNSSE.Tree n) :
    DeciNSSE.covPrefTop w t ↔ ext t w = .top := by
  change Safety.HasLabel t w .top ↔ _
  rw [← Safety.trace_eq_top_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [ext, h]

/-- A bottom prefix is equivalent to a bottom label in the constant extension. -/
@[simp] theorem covPrefBot_iff_ext (w : List (Fin n)) (t : DeciNSSE.Tree n) :
    DeciNSSE.covPrefBot w t ↔ ext t w = .bot := by
  change Safety.HasLabel t w .bot ↔ _
  rw [← Safety.trace_eq_bot_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [ext, h]

/-- The covariant order is the pointwise order of constant leaf extensions. -/
theorem le_iff_ext (t u : DeciNSSE.Tree n) : t ≤ u ↔ ∀ w, ext t w ≤ ext u w := by
  rw [cov_le_iff_safe]
  simp only [covPrefTop_iff_ext, covPrefBot_iff_ext]
  have hs (a b : Sym) : ((a = .top → b = .top) ∧ (b = .bot → a = .bot)) ↔ a ≤ b := by
    cases a <;> cases b <;> decide
  simp only [hs]

/-- The constant leaf extension determines the tree. -/
theorem ext_injective : Function.Injective (@ext n) := by
  intro a b h
  apply _root_.le_antisymm <;> apply (le_iff_ext _ _).mpr <;> intro w <;> rw [h]

/-- Extreme labels remain constant on every descendant. -/
theorem ext_absorb (t : DeciNSSE.Tree n) (w v : List (Fin n)) (h : ext t w ≠ .f) :
    ext t (w ++ v) = ext t w := by
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with ht | ht | ⟨a, ht⟩
  · simp [ext, Safety.trace_append, ht]
  · simp [ext, Safety.trace_append, ht]
  · simp [ext, ht] at h

/-- Constant leaf extension commutes with duality. -/
@[simp] theorem ext_d (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    ext (DeciNSSE.Tree.dual t) w = Sym.flip true (ext t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp [Sym.flip]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Sym.flip]
    · simp [Sym.flip]
    · simp [ih]

/-! ## The median in `⊥ < f < ⊤` -/

/-- The median in the three-element linear order. -/
def medianSym (a b c : Sym) : Sym := max (min a b) (min (max a b) c)

/-- The label median is monotone in all three inputs. -/
theorem medianSym_mono {a a' b b' c c' : Sym}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    medianSym a b c ≤ medianSym a' b' c' :=
  max_le_max (min_le_min ha hb) (min_le_min (max_le_max ha hb) hc)

/-- Two equal labels determine the median. -/
@[simp] theorem medianSym_self (a c : Sym) : medianSym a a c = a := by
  cases a <;> cases c <;> decide

/-- Swapping the first two labels preserves the median. -/
theorem medianSym_swap (a b c : Sym) : medianSym a b c = medianSym b a c := by
  simp [medianSym, min_comm, max_comm]

/-- Flipping all three labels flips their median. -/
theorem medianSym_flip (a b c : Sym) :
    Sym.flip true (medianSym a b c) =
      medianSym (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- An extreme median needs two equal extreme inputs, so absorption is preserved. -/
theorem medianSym_absorb (a b c a' b' c' : Sym)
    (ha : a ≠ .f → a' = a) (hb : b ≠ .f → b' = b) (hc : c ≠ .f → c' = c)
    (h : medianSym a b c ≠ .f) : medianSym a' b' c' = medianSym a b c := by
  cases a <;> cases b <;> cases c <;> simp_all [medianSym]

/-! ## Pruning an absorbing label map -/

/-- Prune at the first extreme label. -/
noncomputable def prune (labels : List (Fin n) → Sym) : DeciNSSE.Tree n := by
  classical
  exact {
    fn := fun w => if DeciNSSE.Active labels w then some (labels w) else none
    wf := by
      constructor
      · simp
      · intro w i
        simp only [DeciNSSE.active_append_singleton]
        by_cases h : DeciNSSE.Active labels w <;> simp [h]
  }

/-- Pruning is a right inverse of constant extension on absorbing label maps. -/
theorem ext_prune (labels : List (Fin n) → Sym)
    (h : ∀ w v, labels w ≠ .f → labels (w ++ v) = labels w) :
    ext (prune labels) = labels := by
  classical
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [ext, prune]
  | append_singleton w i ih =>
    rw [ext_step, ih]
    by_cases ha : DeciNSSE.Active labels (w ++ [i])
    · simp [prune, ha]
    · simp only [prune, ite_eq_right ha, Option.getD_none]
      by_cases hw : labels w = .f
      · obtain ⟨v, hp, hn, hv⟩ := by
          simpa only [DeciNSSE.Active, not_forall, Classical.not_imp] using ha
        have hvw : v.IsPrefix w := List.prefix_of_prefix_length_le hp
          (List.prefix_append _ _) (by
            have hle := hp.length_le
            have hne : v.length ≠ (w ++ [i]).length := fun he => hn (hp.eq_of_length he)
            simp only [List.length_append, List.length_singleton] at hle hne
            omega)
        obtain ⟨s, rfl⟩ := hvw
        exact False.elim (hv ((h v s hv).symm.trans hw))
      · exact (h w [i] hw).symm

/-! ## The median tree -/

/-- The label is the pointwise median; its domain consists of constructor prefixes. -/
noncomputable def treeMedian (a b c : DeciNSSE.Tree n) : DeciNSSE.Tree n :=
  prune (fun w => medianSym (ext a w) (ext b w) (ext c w))

/-- The median is pointwise on constant extensions. -/
@[simp] theorem ext_treeMedian (a b c : DeciNSSE.Tree n) (w : List (Fin n)) :
    ext (treeMedian a b c) w = medianSym (ext a w) (ext b w) (ext c w) := by
  apply congrFun (ext_prune _ _) w
  intro v s h
  exact medianSym_absorb _ _ _ _ _ _ (ext_absorb a v s) (ext_absorb b v s)
    (ext_absorb c v s) h

/-- The tree median is monotone in all three inputs. -/
theorem treeMedian_mono {a a' b b' c c' : DeciNSSE.Tree n}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    treeMedian a b c ≤ treeMedian a' b' c' := by
  apply (le_iff_ext _ _).mpr
  intro w
  simp only [ext_treeMedian]
  exact medianSym_mono ((le_iff_ext _ _).mp ha w) ((le_iff_ext _ _).mp hb w)
    ((le_iff_ext _ _).mp hc w)

/-- Two equal trees determine the median. -/
@[simp] theorem treeMedian_self (a c : DeciNSSE.Tree n) : treeMedian a a c = a := by
  apply ext_injective; funext w; simp

/-- Swapping the first two trees preserves the median. -/
theorem treeMedian_swap (a b c : DeciNSSE.Tree n) : treeMedian a b c = treeMedian b a c := by
  apply ext_injective; funext w; simp [medianSym_swap]

/-- The median commutes with the n-ary constructor, child by child. -/
theorem treeMedian_node (a b c : Fin n → DeciNSSE.Tree n) :
    treeMedian (DeciNSSE.Tree.node a) (DeciNSSE.Tree.node b) (DeciNSSE.Tree.node c) =
      DeciNSSE.Tree.node (fun i => treeMedian (a i) (b i) (c i)) := by
  apply ext_injective; funext w
  cases w with
  | nil => simp
  | cons i w => simp

/-- Duality commutes with the tree median. -/
theorem d_treeMedian (a b c : DeciNSSE.Tree n) :
    DeciNSSE.Tree.dual (treeMedian a b c) =
      treeMedian (DeciNSSE.Tree.dual a) (DeciNSSE.Tree.dual b) (DeciNSSE.Tree.dual c) := by
  apply ext_injective; funext w; simp [medianSym_flip]

end DeciENSSE.Support.Median

namespace DeciENSSE.Support.Median
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
theorem medianSym_eq_f {a b c : Sym} (h : medianSym a b c = .f) :
    a = .f ∨ b = .f ∨ c = .f := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

/-- A constructor median step strictly decreases the sum of the three heights. -/
theorem finiteMedian_decreasing {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f) (i : Fin n) :
    (child a i).height + (child b i).height + (child c i).height <
      a.height + b.height + c.height := by
  have ha := height_child_le a i
  have hb := height_child_le b i
  have hc := height_child_le c i
  rcases medianSym_eq_f h with h | h | h
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega

/-- The median of three finite trees, computed root by root. The hypothesis `_h`
is used by the termination proof. -/
def finiteMedian (a b c : FTree n) : FTree n :=
  if _h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f then
    .node fun i => finiteMedian (child a i) (child b i) (child c i)
  else if medianSym (rootSym a) (rootSym b) (rootSym c) = .bot then .bot else .top
termination_by a.height + b.height + c.height
decreasing_by exact finiteMedian_decreasing _h i

/-- A bottom root median produces the finite bottom tree. -/
theorem finiteMedian_of_bot {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .bot) : finiteMedian a b c = .bot := by
  rw [finiteMedian]; simp [h]

/-- A top root median produces the finite top tree. -/
theorem finiteMedian_of_top {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .top) : finiteMedian a b c = .top := by
  rw [finiteMedian]; simp [h]

/-- A constructor root median recurses on the three selected children. -/
theorem finiteMedian_of_f {a b c : FTree n}
    (h : medianSym (rootSym a) (rootSym b) (rootSym c) = .f) :
    finiteMedian a b c = .node fun i => finiteMedian (child a i) (child b i) (child c i) := by
  rw [finiteMedian]; simp [h]

/-- The constant extension at the root equals the finite root symbol. -/
@[simp] theorem ext_toTree_nil (t : FTree n) : ext t.toTree [] = rootSym t := by
  cases t <;> rfl

/-- The constant extension follows the finite child operation. -/
theorem ext_toTree_cons (t : FTree n) (i : Fin n) (w : List (Fin n)) :
    ext t.toTree (i :: w) = ext (child t i).toTree w := by
  cases t <;> simp

/-- The finite median is pointwise on constant extensions. -/
theorem ext_finiteMedian (a b c : FTree n) (w : List (Fin n)) :
    ext (finiteMedian a b c).toTree w =
      medianSym (ext a.toTree w) (ext b.toTree w) (ext c.toTree w) := by
  induction w generalizing a b c with
  | nil =>
    simp only [ext_toTree_nil]
    cases hm : medianSym (rootSym a) (rootSym b) (rootSym c)
    · rw [finiteMedian_of_bot hm]; rfl
    · rw [finiteMedian_of_f hm]; rfl
    · rw [finiteMedian_of_top hm]; rfl
  | cons i w ih =>
    have habs : ∀ t : FTree n, rootSym t ≠ .f →
        ext t.toTree (i :: w) = rootSym t := fun t ht => by
      have h := ext_absorb t.toTree [] (i :: w) (by simpa using ht)
      simpa using h
    cases hm : medianSym (rootSym a) (rootSym b) (rootSym c) with
    | bot =>
      rw [finiteMedian_of_bot hm]
      have h := medianSym_absorb (rootSym a) (rootSym b) (rootSym c)
        (ext a.toTree (i :: w)) (ext b.toTree (i :: w)) (ext c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | top =>
      rw [finiteMedian_of_top hm]
      have h := medianSym_absorb (rootSym a) (rootSym b) (rootSym c)
        (ext a.toTree (i :: w)) (ext b.toTree (i :: w)) (ext c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | f =>
      rw [finiteMedian_of_f hm, ext_toTree_cons, child_node, ih, ext_toTree_cons a,
        ext_toTree_cons b, ext_toTree_cons c]

/-- `finite_med`: the median of three finite trees is the finite tree `finiteMedian`. -/
@[simp] theorem finiteMedian_toTree (a b c : FTree n) :
    (finiteMedian a b c).toTree = treeMedian a.toTree b.toTree c.toTree := by
  apply ext_injective
  funext w
  rw [ext_finiteMedian, ext_treeMedian]

end DeciENSSE.Support.Median
