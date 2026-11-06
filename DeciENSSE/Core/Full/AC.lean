import DeciENSSE.Core.Basic
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Two observations of a covariant tree

The top leaf cone A (`aobs`) contains paths with a top-labeled prefix. The
nonbottom observation C (`cobs`) contains paths with no bottom-labeled prefix;
it includes paths below top leaves, not just constructor positions. A tree is
determined by C and the complement of A. Every pair of prefix-closed sets
covering all words realizes a tree.

## Main declarations

- `aobs`
- `cobs`
- `Pair`
- `realize`
- `order_iff`
- `realize_observations`
- `realize_ofTree`
-/

namespace DeciENSSE.Core.Full.AC
open DeciNSSE

variable {n : ℕ}

/-- The top leaf cone A: a top label occurs on a prefix of the path. -/
def aobs (t : DeciNSSE.Tree n) (w : List (Fin n)) : Prop :=
  Safety.HasLabel t w Sym.top

/-- The nonbottom observation C: paths with no bottom-labeled prefix. -/
def cobs (t : DeciNSSE.Tree n) : PrefixSet n where
  carrier := {w | ¬ Safety.HasLabel t w Sym.bot}
  prefix_closed := by
    rintro u v h ⟨p, ⟨s, hs⟩, hp⟩
    apply h
    exact ⟨p, ⟨s ++ v, by simpa only [List.append_assoc] using congrArg (fun q => q ++ v) hs⟩, hp⟩

/-- Constructor-observation membership means no prefix is labeled bottom. -/
@[simp] theorem cobs_mem (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    w ∈ (cobs t).carrier ↔ ¬ Safety.HasLabel t w Sym.bot := Iff.rfl

/-- Bottom has no positive top observation. -/
@[simp] theorem aobs_bot (w : List (Fin n)) : ¬ aobs DeciNSSE.Tree.bot w := by simp [aobs]
/-- Top satisfies every positive top observation. -/
@[simp] theorem aobs_top (w : List (Fin n)) : aobs DeciNSSE.Tree.top w := by simp [aobs]
/-- The constructor observation of bottom is empty. -/
@[simp] theorem cobs_bot : cobs (DeciNSSE.Tree.bot : DeciNSSE.Tree n) = PrefixSet.bot := by
  ext w
  simp

/-- The prefix-closed set of all paths. -/
def full : PrefixSet n := ⟨Set.univ, by simp⟩
/-- Every path belongs to the full prefix-closed set. -/
@[simp] theorem mem_full (w : List (Fin n)) : w ∈ full.carrier := trivial
/-- The constructor observation of top contains every path. -/
@[simp] theorem cobs_top : cobs (DeciNSSE.Tree.top : DeciNSSE.Tree n) = full := by ext w; simp

/-- Constructor observation commutes with every constructor child. -/
@[simp] theorem cobs_node (a : Fin n → DeciNSSE.Tree n) :
    cobs (DeciNSSE.Tree.node a) = PrefixSet.node (cobs ∘ a) := by
  ext w
  cases w with
  | nil => simp [Safety.HasLabel]
  | cons i w =>
      simp [Safety.hasLabel_node_cons _ _ _ Sym.bot (by decide)]

/-- Every positive top observation belongs to the constructor observation. -/
theorem aobs_subset_cobs (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    aobs t w → w ∈ (cobs t).carrier := by
  intro ha hc
  have ht := (Safety.trace_eq_top_iff _ _).mpr ha
  have hb := (Safety.trace_eq_bot_iff _ _).mpr hc
  exact DeciNSSE.Tree.bot_ne_top (hb.symm.trans ht)

/-- A bottom prefix of the dual is a top prefix of the original tree. -/
theorem hasLabel_dual (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    Safety.HasLabel (DeciNSSE.Tree.dual t) w Sym.bot ↔ Safety.HasLabel t w Sym.top := by
  simp only [Safety.HasLabel, DeciNSSE.dual_fn, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, hv, s, hs, he⟩
    cases s <;> simp_all [Sym.flip]
    exact ⟨v, hv, hs⟩
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, hv, Sym.top, hs, rfl⟩

/-- The constructor observation of the dual is the complement of the top observation. -/
@[simp] theorem cobs_dual (t : DeciNSSE.Tree n) (w : List (Fin n)) :
    w ∈ (cobs (DeciNSSE.Tree.dual t)).carrier ↔ ¬ aobs t w := hasLabel_dual t _ |>.not

/-- Covariant tree order is inclusion of both observations, reversing the dual one. -/
theorem order_iff (t u : DeciNSSE.Tree n) :
    t ≤ u ↔ cobs t ≤ cobs u ∧ cobs (DeciNSSE.Tree.dual u) ≤ cobs (DeciNSSE.Tree.dual t) := by
  classical
  rw [DeciNSSE.cov_le_iff_safe]
  constructor
  · intro h
    constructor
    · intro w ht hu; exact ht ((h _).2 hu)
    · intro w hu
      simp only [cobs_dual] at hu ⊢
      exact fun ht => hu ((h _).1 ht)
  · rintro ⟨hc, ha⟩ w
    constructor
    · intro ht
      by_contra hu
      exact ((cobs_dual t w).mp (ha ((cobs_dual u w).mpr hu))) ht
    · intro hu
      by_contra ht
      exact hc ht hu

/-- Store C and the complement of A, both prefix closed. -/
structure Pair (n : ℕ) where
  c : PrefixSet n
  n : PrefixSet n
  cover : ∀ w, w ∈ c.carrier ∨ w ∈ n.carrier

/-- Store the constructor observation and the complement of the top observation. -/
def ofTree (t : DeciNSSE.Tree n) : Pair n :=
  ⟨cobs t, cobs (DeciNSSE.Tree.dual t), fun w => by
    classical
    by_cases ha : aobs t w
    · exact Or.inl (aobs_subset_cobs t w ha)
    · exact Or.inr ((cobs_dual t w).mpr ha)⟩

/-- Restrict both observations to paths beginning with the chosen child. -/
def Pair.child (p : Pair n) (b : Fin n) : Pair n :=
  ⟨p.c.subtree b, p.n.subtree b, fun w => p.cover (b :: w)⟩

attribute [local instance] Classical.propDecidable

private noncomputable def pairFn (p : Pair n) : List (Fin n) → Option Sym
  | [] => if [] ∉ p.c.carrier then some Sym.bot else
      if [] ∉ p.n.carrier then some Sym.top else some Sym.f
  | b :: w => if [] ∈ p.c.carrier ∧ [] ∈ p.n.carrier then pairFn (p.child b) w else none

private theorem pairFn_child (p : Pair n) (w : List (Fin n)) (b : Fin n) :
    (pairFn p (w ++ [b])).isSome ↔ pairFn p w = some Sym.f := by
  classical
  induction w generalizing p with
  | nil => simp only [List.nil_append, pairFn]; split_ifs <;> simp_all
  | cons a w ih =>
    simp only [List.cons_append, pairFn]
    split_ifs <;> simp_all

/-- Realize a covering pair of prefix-closed observations as a tree. -/
noncomputable def realize (p : Pair n) : DeciNSSE.Tree n where
  fn := pairFn p
  wf := by
    constructor
    · classical
      simp only [pairFn]
      split_ifs <;> simp
    · exact pairFn_child p

/-- Absence of the empty constructor observation forces bottom. -/
theorem realize_bot (p : Pair n) (h : [] ∉ p.c.carrier) : realize p = DeciNSSE.Tree.bot := by
  classical
  apply (DeciNSSE.Tree.root_eq_bot_iff _).mp
  simp [realize, pairFn, h]

/-- Absence of the empty dual-constructor observation forces top. -/
theorem realize_top (p : Pair n) (h : [] ∉ p.n.carrier) : realize p = DeciNSSE.Tree.top := by
  classical
  have hc : [] ∈ p.c.carrier := (p.cover []).resolve_right h
  apply (DeciNSSE.Tree.root_eq_top_iff _).mp
  simp [realize, pairFn, h, hc]

/-- Two present root observations yield a constructor of the child realizations. -/
theorem realize_node (p : Pair n) (hc : [] ∈ p.c.carrier) (hn : [] ∈ p.n.carrier) :
    realize p = DeciNSSE.Tree.node (fun i => realize (p.child i)) := by
  classical
  apply DeciNSSE.Tree.ext
  funext w
  cases w with
  | nil => simp [realize, pairFn, hc, hn]
  | cons i w => simp [realize, pairFn, hc, hn]

/-- The realized tree has exactly the specified observations. -/
theorem realize_observations (p : Pair n) (w : List (Fin n)) :
    (w ∈ (cobs (realize p)).carrier ↔ w ∈ p.c.carrier) ∧
    (aobs (realize p) w ↔ w ∉ p.n.carrier) := by
  classical
  induction w generalizing p with
  | nil =>
    by_cases hc : [] ∈ p.c.carrier
    · by_cases hn : [] ∈ p.n.carrier
      · rw [realize_node p hc hn]
        simp [aobs, hc, hn]
      · rw [realize_top p hn]; simp [hc, hn]
    · have hn := (p.cover []).resolve_left hc
      rw [realize_bot p hc]; simp [hc, hn]
  | cons b w ih =>
    by_cases hc : [] ∈ p.c.carrier
    · by_cases hn : [] ∈ p.n.carrier
      · rw [realize_node p hc hn]
        have hh := ih (p.child b)
        simpa [cobs_node, aobs,
          Safety.hasLabel_node_cons _ _ _ Sym.bot (by decide),
        Safety.hasLabel_node_cons _ _ _ Sym.top (by decide), Pair.child,
          PrefixSet.subtree, PrefixSet.residual] using hh
      · have hn' : b :: w ∉ p.n.carrier := fun h => hn (p.n.prefix_closed [] _ h)
        have hc' := (p.cover (b :: w)).resolve_right hn'
        rw [realize_top p hn]; simp [hc', hn']
    · have hc' : b :: w ∉ p.c.carrier := fun h => hc (p.c.prefix_closed [] _ h)
      have hn' := (p.cover (b :: w)).resolve_left hc'
      rw [realize_bot p hc]; simp [hc', hn']

/-- Realization has the specified constructor observation. -/
@[simp] theorem cobs_realize (p : Pair n) : cobs (realize p) = p.c := by
  ext w; exact (realize_observations p w).1

/-- The dual of the realization has the specified second observation. -/
@[simp] theorem cobs_dual_realize (p : Pair n) : cobs (DeciNSSE.Tree.dual (realize p)) = p.n := by
  classical
  ext w; rw [cobs_dual, (realize_observations p w).2]; simp

/-- Equal constructor and dual-constructor observations determine equal trees. -/
theorem observations_injective {t u : DeciNSSE.Tree n}
    (hc : cobs t = cobs u) (hn : cobs (DeciNSSE.Tree.dual t) = cobs (DeciNSSE.Tree.dual u)) : t = u
      := by
  apply le_antisymm
  · exact (order_iff t u).mpr (by simp [hc, hn])
  · exact (order_iff u t).mpr (by simp [hc, hn])

/-- Realizing the observations of a tree recovers that tree. -/
@[simp] theorem realize_ofTree (t : DeciNSSE.Tree n) : realize (ofTree t) = t :=
  observations_injective (cobs_realize _) (cobs_dual_realize _)

end DeciENSSE.Core.Full.AC
