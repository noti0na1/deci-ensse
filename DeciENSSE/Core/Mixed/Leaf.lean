import DeciENSSE.Core.Full.AC
import DeciENSSE.Core.Full.Basic
import DeciENSSE.Support.Normalization

/-! # Signed leaf coordinates for arbitrary variance

The positive and negative leaf cones record top and bottom after variance
normalization. Each leaf contributes all extensions of its path. These two
disjoint cones determine a tree at every arity; their intersection supplies the
information operation used to combine solutions.

## Main declarations

- `leaf`, `LeafPair`, `treeLe_iff_leaf`, `leaf_dual`,
  `infoInter`, `leaf_infoInter`.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

/-- Both signs are positive membership predicates. -/
def leaf (c : Fin n → Bool) (t : Tree n) (s : Bool) : Set (List (Fin n)) :=
  {w | AC.aobs (DeciNSSE.Tree.normalize c s t) w}

/-- The negative cone complements the normalized non-bottom observation. -/
theorem leaf_minus (c : Fin n → Bool) (t : Tree n) (w : List (Fin n)) :
    w ∈ leaf c t true ↔ w ∉ (AC.cobs (DeciNSSE.Tree.normalize c false t)).carrier := by
  classical
  rw [leaf, Set.mem_ofPred, normalize_true]
  have h := AC.cobs_dual (DeciNSSE.Tree.dual (DeciNSSE.Tree.normalize c false t)) w
  simpa using h.not.symm

/-- **Leaf representation** (3), duality of cones (`thm:lf-representation`(3)):
`L^s_{t∂} = L^{1-s}_t`. -/
theorem leaf_dual (c : Fin n → Bool) (t : Tree n) (s : Bool) :
    leaf c (DeciNSSE.Tree.dual t) s = leaf c t (!s) := by
  simp only [leaf, Support.normalize_dual]

/-- Membership persists under arbitrary right extensions. -/
def ExtensionClosed (A : Set (List (Fin n))) : Prop := ∀ u v, u ∈ A → u ++ v ∈ A

/-- Two disjoint, extension-closed signed leaf cones. -/
structure LeafPair (n : ℕ) where
  cone : Bool → Set (List (Fin n))
  extension : ∀ s, ExtensionClosed (cone s)
  disjoint : ∀ w, w ∈ cone false → w ∈ cone true → False

/-- A leaf pair is determined by its cones. -/
@[ext] theorem LeafPair.ext {p q : LeafPair n} (h : p.cone = q.cone) : p = q := by
  cases p; cases q; cases h; rfl

/-- Leaf cones are extension closed. -/
theorem leaf_extension (c : Fin n → Bool) (t : Tree n) (s : Bool) :
    ExtensionClosed (leaf c t s) := by
  intro u v h
  obtain ⟨p, ⟨z, hz⟩, hp⟩ := h
  exact ⟨p, ⟨z ++ v, by
      simpa [List.append_assoc] using congrArg (fun q => q ++ v) hz⟩, hp⟩

/-- A word cannot belong to both signed leaf cones. -/
theorem leaf_disjoint (c : Fin n → Bool) (t : Tree n) (w : List (Fin n)) :
    w ∈ leaf c t false → w ∈ leaf c t true → False := by
  intro hp hm
  exact (leaf_minus c t w).mp hm (AC.aobs_subset_cobs _ _ hp)

/-- The signed leaf coordinates of a tree. -/
def leafPair (c : Fin n → Bool) (t : Tree n) : LeafPair n :=
  ⟨leaf c t, leaf_extension c t, leaf_disjoint c t⟩

/-- Complementing the two cones gives the A/C representation of `Core.Full.AC`. -/
def LeafPair.toAC (p : LeafPair n) : AC.Pair n where
  c := ⟨(p.cone true)ᶜ, fun u v h hu => h (p.extension true u v hu)⟩
  n := ⟨(p.cone false)ᶜ, fun u v h hu => h (p.extension false u v hu)⟩
  cover w := by
    classical
    by_cases hp : w ∈ p.cone false
    · exact Or.inl (fun hm => p.disjoint w hp hm)
    · exact Or.inr hp

/-- Realize a leaf pair as a tree with the specified variance. -/
noncomputable def decode (c : Fin n → Bool) (p : LeafPair n) : Tree n :=
  DeciNSSE.Tree.normalize c false (AC.realize p.toAC)

/-- Realization recovers each signed cone. -/
@[simp] theorem leaf_decode (c : Fin n → Bool) (p : LeafPair n) (s : Bool) :
    leaf c (decode c p) s = p.cone s := by
  classical
  ext w
  cases s with
  | false =>
    change AC.aobs (DeciNSSE.Tree.normalize c false (DeciNSSE.Tree.normalize c false _)) w ↔ _
    rw [normalize_involutive, (AC.realize_observations p.toAC w).2]
    simp [LeafPair.toAC]
  | true =>
    rw [leaf_minus]
    simp [decode, LeafPair.toAC]

/-- Subtype order is inclusion in the positive cone and reverse inclusion in the negative cone. -/
theorem treeLe_iff_leaf (c : Fin n → Bool) (t u : Tree n) :
    DeciNSSE.Tree.Le c t u ↔ leaf c t false ⊆ leaf c u false ∧
      leaf c u true ⊆ leaf c t true := by
  rw [treeLe_iff_normalize, cov_le_iff_safe]
  constructor
  · intro h
    constructor
    · intro w hw; exact (h w).1 hw
    · intro w hw
      have hm : ∀ t, w ∈ leaf c t true ↔
          DeciNSSE.Safety.HasLabel (DeciNSSE.Tree.normalize c false t) w Sym.bot :=
        fun t => by
          classical
          simpa [AC.cobs] using leaf_minus c t w
      exact (hm t).mpr ((h w).2 ((hm u).mp hw))
  · rintro ⟨hp, hm⟩ w
    constructor
    · exact hp (a := w)
    · classical
      simpa only [leaf_minus, AC.cobs_mem, not_not] using hm (a := w)

/-- Signed leaf coordinates determine the tree. -/
theorem leaf_injective (c : Fin n → Bool) {t u : Tree n}
    (h : ∀ s, leaf c t s = leaf c u s) : t = u := by
  apply treeLe_antisymm (c := c)
  · exact (treeLe_iff_leaf c t u).mpr (by simp [h])
  · exact (treeLe_iff_leaf c u t).mpr (by simp [h])

/-- Bottom contains every word in its negative cone only. -/
@[simp] theorem leaf_bot (c : Fin n → Bool) (s : Bool) (w : List (Fin n)) :
    w ∈ leaf c DeciNSSE.Tree.bot s ↔ s = true := by
  cases s <;> simp [leaf]

/-- Top contains every word in its positive cone only. -/
@[simp] theorem leaf_top (c : Fin n → Bool) (s : Bool) (w : List (Fin n)) :
    w ∈ leaf c DeciNSSE.Tree.top s ↔ s = false := by
  cases s <;> simp [leaf]

/-- A constructor has neither leaf label at the root. -/
@[simp] theorem leaf_node_nil (c : Fin n → Bool) (a : Fin n → Tree n) (s : Bool) :
    [] ∉ leaf c (DeciNSSE.Tree.node a) s := by
  simp [leaf, AC.aobs]

/-- A constructor child changes sign according to its variance. -/
@[simp] theorem leaf_node_cons (c : Fin n → Bool) (a : Fin n → Tree n)
    (s : Bool) (i : Fin n) (w : List (Fin n)) :
    i :: w ∈ leaf c (DeciNSSE.Tree.node a) s ↔
      w ∈ leaf c (a i) (Bool.xor s (c i)) := by
  simp only [leaf, Set.mem_ofPred_eq, AC.aobs, normalize_node,
    DeciNSSE.Safety.hasLabel_node_cons _ _ _ Sym.top (by decide)]

/-- A negative root leaf characterizes bottom. -/
@[simp] theorem leaf_root_minus (c : Fin n → Bool) (t : Tree n) :
    [] ∈ leaf c t true ↔ t = DeciNSSE.Tree.bot := by
  classical
  rw [leaf_minus]
  simp [AC.cobs]

/-- A positive root leaf characterizes top. -/
@[simp] theorem leaf_root_plus (c : Fin n → Bool) (t : Tree n) :
    [] ∈ leaf c t false ↔ t = DeciNSSE.Tree.top := by
  simp [leaf, AC.aobs]

/-- Intersect both signed cones of two leaf pairs. -/
def LeafPair.inter (p q : LeafPair n) : LeafPair n where
  cone s := p.cone s ∩ q.cone s
  extension s u v h := ⟨p.extension s u v h.1, q.extension s u v h.2⟩
  disjoint w hp hm := p.disjoint w hp.1 hm.1

/-- Information intersection, rather than the subtype meet. -/
noncomputable def infoInter (c : Fin n → Bool) (t u : Tree n) : Tree n :=
  decode c ((leafPair c t).inter (leafPair c u))

/-- Information intersection intersects each signed cone. -/
@[simp] theorem leaf_infoInter (c : Fin n → Bool) (t u : Tree n) (s : Bool) :
    leaf c (infoInter c t u) s = leaf c t s ∩ leaf c u s := leaf_decode _ _ _

/-- The all-constructor tree has neither signed leaf cone. -/
@[simp] theorem leaf_allF (c : Fin n → Bool) (s : Bool) :
    leaf c (RGraph.allF n).unfold s = ∅ := by
  have h : ∀ (w : List (Fin n)) s, w ∉ leaf c (RGraph.allF n).unfold s := by
    intro w
    induction w with
    | nil =>
      intro s
      rw [RGraph.allF_unfold_node]
      exact leaf_node_nil c _ s
    | cons i w ih =>
      intro s
      rw [RGraph.allF_unfold_node, leaf_node_cons]
      exact ih _
  ext w
  simp [h]

/-- Information intersection of the two extremes is Ωₙ, even at n = 0. -/
theorem infoInter_bot_top (c : Fin n → Bool) :
    infoInter c DeciNSSE.Tree.bot DeciNSSE.Tree.top = (RGraph.allF n).unfold := by
  apply leaf_injective c
  intro s
  ext w
  cases s <;> simp

/-- A chosen child gives an infinite branch; no finite presentation can realize Ωₙ. -/
theorem allF_not_finite (i : Fin n) :
    ¬ ∃ a : FTree n, a.toTree = (RGraph.allF n).unfold := by
  rintro ⟨a, ha⟩
  induction a with
  | bot =>
    rw [FTree.toTree_bot, RGraph.allF_unfold_node] at ha
    exact DeciNSSE.Tree.node_ne_bot _ ha.symm
  | top =>
    rw [FTree.toTree_top, RGraph.allF_unfold_node] at ha
    exact DeciNSSE.Tree.node_ne_top _ ha.symm
  | node a ih =>
    rw [FTree.toTree_node, RGraph.allF_unfold_node] at ha
    exact ih i (congrFun ((DeciNSSE.Tree.node_eq_node_iff _ _).mp ha) i)

end DeciENSSE.Core.Mixed
