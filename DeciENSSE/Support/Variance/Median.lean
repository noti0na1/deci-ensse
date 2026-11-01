import DeciNSSE.Constraints.Signed
import DeciNSSE.Satisfiability.LeastShape


/-! # Median closure of trees

Constant leaf extensions embed tree order into pointwise label order. Pruning
the pointwise median gives a tree and preserves constructors and duality.

## Main declarations

- `extN`
- `medN`
- `extN_medN`
- `medN_mono`
- `medN_node`
- `d_medN`
-/

namespace DeciENSSE.Support
open DeciNSSE

open DeciNSSE.Tree

variable {n : ℕ}

/-! ## Constant leaf extension -/

/-- Read the root of the leaf-freezing trace: the label at `w`, or the first leaf
above `w` when `w` leaves the domain. -/
def extN (t : DeciNSSE.Tree n) (w : List (Fin n)) : Sym :=
  ((Safety.trace t w).fn []).getD .f

/-- The constant leaf extension of bottom is bottom at every path. -/
@[simp] theorem extN_bot (w : List (Fin n)) : extN DeciNSSE.Tree.bot w = .bot := by simp [extN]
/-- The constant leaf extension of top is top at every path. -/
@[simp] theorem extN_top (w : List (Fin n)) : extN DeciNSSE.Tree.top w = .top := by simp [extN]
/-- A constructor has constructor label at the empty path. -/
@[simp] theorem extN_node_nil (a : Fin n → DeciNSSE.Tree n) : extN (DeciNSSE.Tree.node a) [] = .f :=
  rfl
/-- The extension of a constructor follows the selected child. -/
@[simp] theorem extN_node_cons (a : Fin n → DeciNSSE.Tree n) (i : Fin n) (w : List (Fin n)) :
    extN (DeciNSSE.Tree.node a) (i :: w) = extN (a i) w := by
  simp [extN]

/-- At a present position the constant extension agrees with the tree label. -/
theorem extN_of_fn {t : DeciNSSE.Tree n} {w : List (Fin n)} {s : Sym}
    (h : t.fn w = some s) : extN t w = s := by
  induction w generalizing t with
  | nil => simp [extN, h]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp at h
    · simp at h
    · rw [extN_node_cons]; exact ih (by simpa using h)

/-- One trace step uses the next label or retains the preceding extreme label. -/
theorem extN_step (t : DeciNSSE.Tree n) (w : List (Fin n)) (i : Fin n) :
    extN t (w ++ [i]) = (t.fn (w ++ [i])).getD (extN t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simp [extN]
  | cons j w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simpa using ih (t := a j)

/-- A top prefix is equivalent to a top label in the constant extension. -/
@[simp] theorem covPrefTopN_iff_extN (w : List (Fin n)) (t : DeciNSSE.Tree n) :
    DeciNSSE.covPrefTop w t ↔ extN t w = .top := by
  change Safety.HasLabel t w .top ↔ _
  rw [← Safety.trace_eq_top_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extN, h]

/-- A bottom prefix is equivalent to a bottom label in the constant extension. -/
@[simp] theorem covPrefBotN_iff_extN (w : List (Fin n)) (t : DeciNSSE.Tree n) :
    DeciNSSE.covPrefBot w t ↔ extN t w = .bot := by
  change Safety.HasLabel t w .bot ↔ _
  rw [← Safety.trace_eq_bot_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [extN, h]

/-- The covariant order is the pointwise order of constant leaf extensions. -/
theorem le_iff_extN (t u : DeciNSSE.Tree n) : t ≤ u ↔ ∀ w, extN t w ≤ extN u w := by
  rw [cov_le_iff_safe]
  simp only [covPrefTopN_iff_extN, covPrefBotN_iff_extN]
  have hs (a b : Sym) : ((a = .top → b = .top) ∧ (b = .bot → a = .bot)) ↔ a ≤ b := by
    cases a <;> cases b <;> decide
  simp only [hs]

/-- The constant leaf extension determines the tree. -/
theorem extN_injective : Function.Injective (@extN n) := by
  intro a b h
  apply _root_.le_antisymm <;> apply (le_iff_extN _ _).mpr <;> intro w <;> rw [h]

/-- Extreme labels remain constant on every descendant. -/
theorem extN_absorb (t : DeciNSSE.Tree n) (w v : List (Fin n)) (h : extN t w ≠ .f) :
    extN t (w ++ v) = extN t w := by
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with ht | ht | ⟨a, ht⟩
  · simp [extN, Safety.trace_append, ht]
  · simp [extN, Safety.trace_append, ht]
  · simp [extN, ht] at h


/-- Constant leaf extension commutes with duality. -/
@[simp] theorem extN_d (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    extN (DeciNSSE.Tree.dual t) w = Sym.flip true (extN t w) := by
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
def medianSymN (a b c : Sym) : Sym := max (min a b) (min (max a b) c)

/-- The label median is monotone in all three inputs. -/
theorem medianSymN_mono {a a' b b' c c' : Sym}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    medianSymN a b c ≤ medianSymN a' b' c' :=
  max_le_max (min_le_min ha hb) (min_le_min (max_le_max ha hb) hc)

/-- Two equal labels determine the median. -/
@[simp] theorem medianSymN_self (a c : Sym) : medianSymN a a c = a := by
  cases a <;> cases c <;> decide

/-- Swapping the first two labels preserves the median. -/
theorem medianSymN_swap (a b c : Sym) : medianSymN a b c = medianSymN b a c := by
  simp [medianSymN, min_comm, max_comm]

/-- Flipping all three labels flips their median. -/
theorem medianSymN_flip (a b c : Sym) :
    Sym.flip true (medianSymN a b c) =
      medianSymN (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- An extreme median needs two equal extreme inputs, so absorption is preserved. -/
theorem medianSymN_absorb (a b c a' b' c' : Sym)
    (ha : a ≠ .f → a' = a) (hb : b ≠ .f → b' = b) (hc : c ≠ .f → c' = c)
    (h : medianSymN a b c ≠ .f) : medianSymN a' b' c' = medianSymN a b c := by
  cases a <;> cases b <;> cases c <;> simp_all [medianSymN]

/-! ## Pruning an absorbing label map -/

/-- Prune at the first extreme label. -/
noncomputable def pruneN (labels : List (Fin n) → Sym) : DeciNSSE.Tree n := by
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
theorem extN_pruneN (labels : List (Fin n) → Sym)
    (h : ∀ w v, labels w ≠ .f → labels (w ++ v) = labels w) :
    extN (pruneN labels) = labels := by
  classical
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [extN, pruneN]
  | append_singleton w i ih =>
    rw [extN_step, ih]
    by_cases ha : DeciNSSE.Active labels (w ++ [i])
    · simp [pruneN, ha]
    · simp only [pruneN, ite_eq_right ha, Option.getD_none]
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
noncomputable def medN (a b c : DeciNSSE.Tree n) : DeciNSSE.Tree n :=
  pruneN (fun w => medianSymN (extN a w) (extN b w) (extN c w))


/-- The median is pointwise on constant extensions. -/
@[simp] theorem extN_medN (a b c : DeciNSSE.Tree n) (w : List (Fin n)) :
    extN (medN a b c) w = medianSymN (extN a w) (extN b w) (extN c w) := by
  apply congrFun (extN_pruneN _ _) w
  intro v s h
  exact medianSymN_absorb _ _ _ _ _ _ (extN_absorb a v s) (extN_absorb b v s)
    (extN_absorb c v s) h

/-- The tree median is monotone in all three inputs. -/
theorem medN_mono {a a' b b' c c' : DeciNSSE.Tree n} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    medN a b c ≤ medN a' b' c' := by
  apply (le_iff_extN _ _).mpr
  intro w
  simp only [extN_medN]
  exact medianSymN_mono ((le_iff_extN _ _).mp ha w) ((le_iff_extN _ _).mp hb w)
    ((le_iff_extN _ _).mp hc w)


/-- Two equal trees determine the median. -/
@[simp] theorem medN_self (a c : DeciNSSE.Tree n) : medN a a c = a := by
  apply extN_injective; funext w; simp

/-- Swapping the first two trees preserves the median. -/
theorem medN_swap (a b c : DeciNSSE.Tree n) : medN a b c = medN b a c := by
  apply extN_injective; funext w; simp [medianSymN_swap]

/-- The median commutes with the n-ary constructor, child by child. -/
theorem medN_node (a b c : Fin n → DeciNSSE.Tree n) :
    medN (DeciNSSE.Tree.node a) (DeciNSSE.Tree.node b) (DeciNSSE.Tree.node c) =
      DeciNSSE.Tree.node (fun i => medN (a i) (b i) (c i)) := by
  apply extN_injective; funext w
  cases w with
  | nil => simp
  | cons i w => simp

/-- Duality commutes with the tree median. -/
theorem d_medN (a b c : DeciNSSE.Tree n) : DeciNSSE.Tree.dual (medN a b c) = medN
  (DeciNSSE.Tree.dual a) (DeciNSSE.Tree.dual b) (DeciNSSE.Tree.dual c) := by
  apply extN_injective; funext w; simp [medianSymN_flip]

end DeciENSSE.Support
