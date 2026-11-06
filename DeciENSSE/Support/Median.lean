import Mathlib.Data.Set.Finite.List
import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.LeastShape
import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Semantics.Characterization

/-! # Tree medians and finite realization

Constant leaf extensions embed tree order into pointwise label order. Pruning
the pointwise median gives a tree and preserves constructors and duality
(`lem:tc-median`). Beyond the depth of three finite trees their extensions
carry extreme labels only, so the median of three finite trees is finite.

## Main declarations

- `ext`
- `treeMedian`
- `ext_treeMedian`
- `treeMedian_mono`
- `treeMedian_node`
- `d_treeMedian`
- `finite_treeMedian`, `exists_ftree_treeMedian`
- `Median.finD`
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

/-- The constant extension has the constructor label exactly at the
constructor positions of the tree. -/
theorem ext_eq_f_iff (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    ext t w = .f ↔ t.fn w = some .f := by
  refine ⟨fun h => ?_, ext_of_fn⟩
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp_all
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp at h
    · simp at h
    · simpa using ih (a i) (by simpa using h)

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

/-- A constructor median needs a constructor input. -/
theorem medianSym_eq_f {a b c : Sym} (h : medianSym a b c = .f) :
    a = .f ∨ b = .f ∨ c = .f := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

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

/-- **Median** (3) (`lem:tc-median`(3)). The median of three finite trees is
finite. Let `h` bound the lengths of their positions. At a word of length
`h + 1` the constant extensions of all three trees are extreme labels, so is
their median, and the median has no constructor there; since every proper
prefix of a position is a constructor, the positions of the median have length
at most `h + 1`. -/
theorem finite_treeMedian {a b c : DeciNSSE.Tree n}
    (ha : (Characterization.domain a).Finite) (hb : (Characterization.domain b).Finite)
    (hc : (Characterization.domain c).Finite) :
    (Characterization.domain (treeMedian a b c)).Finite := by
  obtain ⟨h, hh⟩ := ((ha.union (hb.union hc)).image List.length).bddAbove
  have hdeep : ∀ t : DeciNSSE.Tree n,
      Characterization.domain t ⊆
        Characterization.domain a ∪ (Characterization.domain b ∪ Characterization.domain c) →
      ∀ w : List (Fin n), h < w.length → ext t w ≠ .f := by
    intro t ht w hw hf
    have hmem : w ∈ Characterization.domain t := by
      simp [Characterization.domain, (ext_eq_f_iff t w).mp hf]
    have := hh ⟨w, ht hmem, rfl⟩
    omega
  apply (List.finite_length_le (Fin n) (h + 1)).subset
  intro π hπ
  show π.length ≤ h + 1
  by_contra hlen
  have hne : π.take (h + 1) ≠ π := fun he => by
    have := congrArg List.length he
    simp at this
    omega
  have hf := (ext_eq_f_iff _ _).mpr
    ((treeMedian a b c).label_eq_f_of_proper_prefix (List.take_prefix _ _) hne hπ)
  rw [ext_treeMedian] at hf
  have hlt : h < (π.take (h + 1)).length := by simp; omega
  rcases medianSym_eq_f hf with hf | hf | hf
  · exact hdeep a (fun _ hw => Or.inl hw) _ hlt hf
  · exact hdeep b (fun _ hw => Or.inr (Or.inl hw)) _ hlt hf
  · exact hdeep c (fun _ hw => Or.inr (Or.inr hw)) _ hlt hf

/-- The median of three finite terms is presented by a finite term. -/
theorem exists_ftree_treeMedian (a b c : FTree n) :
    ∃ m : FTree n, m.toTree = treeMedian a.toTree b.toTree c.toTree :=
  (Characterization.toTree_range_iff _).mpr
    (finite_treeMedian (Characterization.domain_toTree_finite a)
      (Characterization.domain_toTree_finite b) (Characterization.domain_toTree_finite c))

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

end DeciENSSE.Support.Median
