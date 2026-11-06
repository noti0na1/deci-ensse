import DeciENSSE.Semantics
import DeciENSSE.Core.Full.Basic
import DeciENSSE.Core.Mixed.Leaf
import DeciNSSE.Satisfiability.Cycle

/-! # Trees without top: the top-freeness gadget

Let the constructor `f` be covariant. The *gadget* on a variable `v`, with a fresh variable
`y`, is the pair of literals `v ≤ y ∧ y ≤ f(y, …, y)`. It forces `v` to be top-free, and in
each tree class every top-free tree `t` has a witness `y`: the regular tree `Ω = f(Ω, …, Ω)`
for arbitrary and regular trees, and the full finite tree `T_{h(t)+1}` for finite trees.

Adding the gadget for every visible and every hidden variable therefore reduces existential
entailment over `{⊥, f}`, where all values are top-free, to existential entailment over
`{⊥, f, ⊤}` in the same tree class (`TopFree.existsEntailsTIn_iff_gadget`). The visible
carrier `X` becomes `X ⊕ X` and the hidden carrier `Z` becomes `Z ⊕ Z`, the right copies
holding the witnesses. The three deciders for `{⊥, f}` in `DeciENSSE.Main` are built on this
reduction.

## Main declarations

- `TopFree.of_isWitness`: if `t ≤ y ≤ f(y, …, y)`, then `y` and `t` are top-free (the gadget
  lemma, part 1, from `TopFree.of_le_node` and `TopFree.mono`).
- `TopFree.isWitness_allF`, `FTree.full`, `FTree.isWitness_full`: the witnesses `Ω` and
  `T_{h(t)+1}`, with the height `FTree.height` of the shared library (the gadget lemma,
  part 2).
- `TopFree.HasWitnesses`: a tree class in which every top-free tree has a witness;
  `hasWitnesses_all`, `hasWitnesses_reg` and `hasWitnesses_fin` for the three classes.
- `TopFree.gadget`, `TopFree.gadgetAnte`, `TopFree.gadgetCons`: the translation, which adds
  two literals per variable (`length_gadgetAnte`, `length_gadgetCons`).
- `TopFree.existsEntailsTIn_iff_gadget`: the reduction in a class with witnesses, with the
  instances `existsEntailsT_iff_gadget`, `existsEntailsTReg_iff_gadget` and
  `existsEntailsTFin_iff_gadget`.
- `TopFree.le_iff_constructor_subset`, with `le_of_constructor_subset` and
  `constructor_subset_of_le`: on top-free trees the covariant order is inclusion of
  constructor positions.
-/

namespace DeciENSSE
open DeciNSSE Core.Full

variable {n : ℕ}

namespace TopFree

/-! ## Top-free trees -/

/-- The bottom tree is top-free. -/
@[simp] protected theorem bot : TopFree (Tree.bot : Tree n) := by
  intro w; cases w <;> simp

/-- A constructor tree is top-free exactly when all its children are. -/
theorem node_iff (a : Fin n → Tree n) :
    TopFree (DeciNSSE.Tree.node a) ↔ ∀ i, TopFree (a i) := by
  constructor
  · intro h i w; simpa using h (i :: w)
  · intro h w
    cases w with
    | nil => simp
    | cons i w => simpa using h i w

/-- A tree is top-free exactly when its covariant leaf cone of sign 0, the set of words with
a prefix labeled `⊤`, is empty. -/
theorem iff_leaf (t : Tree n) :
    TopFree t ↔ Core.Mixed.leaf (fun _ => false) t false = ∅ := by
  simp only [Core.Mixed.leaf, normalize_false_variance, AC.aobs, Safety.HasLabel,
    Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_exists, not_and]
  constructor
  · exact fun ht _ p _ hp => ht p hp
  · exact fun h w hw => h w w (List.prefix_refl w) hw

/-- `y ≤ f(y, …, y)` forces `y` to be top-free: the sign-0 cone `L` of `y` satisfies
`L ⊆ ⋃ᵢ i L`, so it has no shortest word. -/
theorem of_le_node {y : Tree n} (hy : y ≤ DeciNSSE.Tree.node fun _ => y) : TopFree y := by
  have hle := ((Core.Mixed.treeLe_iff_leaf (fun _ => false) _ _).mp
    ((treeLe_false_iff_le _ _).mpr hy)).1
  rw [iff_leaf, Set.eq_empty_iff_forall_notMem]
  intro w
  induction w with
  | nil => exact fun hw => Core.Mixed.leaf_node_nil _ _ _ (hle hw)
  | cons i w ih =>
    intro hw
    have hc := hle hw
    rw [Core.Mixed.leaf_node_cons] at hc
    exact ih (by simpa using hc)

/-- Every tree below a top-free tree is top-free. -/
theorem mono {t u : Tree n} (hu : TopFree u) (h : t ≤ u) : TopFree t := by
  rw [iff_leaf] at hu ⊢
  have hle := ((Core.Mixed.treeLe_iff_leaf (fun _ => false) t u).mp
    ((treeLe_false_iff_le _ _).mpr h)).1
  exact Set.subset_empty_iff.mp (hu ▸ hle)

/-! ## Gadget witnesses -/

/-- `y` is a gadget witness for `t`: `t ≤ y ≤ f(y, …, y)`. -/
def IsWitness (t y : Tree n) : Prop := t ≤ y ∧ y ≤ DeciNSSE.Tree.node fun _ => y

/-- **The gadget lemma, part 1.** A tree with a gadget witness is top-free. -/
theorem of_isWitness {t y : Tree n} (h : IsWitness t y) : TopFree t :=
  (of_le_node h.2).mono h.1

/-- **The gadget lemma, part 2, regular witness.** `Ω = f(Ω, …, Ω)` is a gadget witness for
every top-free tree. -/
theorem isWitness_allF {t : Tree n} (ht : TopFree t) : IsWitness t (RGraph.allF n).unfold := by
  refine ⟨?_, le_of_eq RGraph.allF_unfold_node⟩
  rw [← treeLe_false_iff_le, Core.Mixed.treeLe_iff_leaf, Core.Mixed.leaf_allF,
    Core.Mixed.leaf_allF, (iff_leaf t).mp ht]
  exact ⟨le_rfl, Set.empty_subset _⟩

end TopFree

end DeciENSSE

/-! ## The full finite trees -/

namespace DeciNSSE.FTree
open DeciENSSE
variable {n : ℕ}

/-- The full finite trees `T₀ = ⊥` and `T_{k+1} = f(T_k, …, T_k)`: the positions of `T_k`
are the words of length at most `k`, labeled `f` below length `k` and `⊥` at length `k`. -/
def full : ℕ → FTree n
  | 0 => bot
  | k + 1 => node fun _ => full k

@[simp] theorem full_zero : (full 0 : FTree n) = bot := rfl

@[simp] theorem full_succ (k : ℕ) : (full (k + 1) : FTree n) = node fun _ => full k := rfl

/-- `T_k ≤ T_{k+1} = f(T_k, …, T_k)`. -/
theorem full_le_node (k : ℕ) :
    (full k : FTree n).toTree ≤ Tree.node fun _ => (full k).toTree := by
  induction k with
  | zero => exact Tree.bot_le _
  | succ k ih => simpa using fun _ => ih

/-- A top-free finite tree `t` lies below `T_k` for every `k ≥ h(t)`, where the height `h(t)`
counts the constructors on a longest path (`FTree.height`). -/
theorem toTree_le_full {a : FTree n} (ha : TopFree a.toTree) {k : ℕ} (hk : a.height ≤ k) :
    a.toTree ≤ (full k).toTree := by
  induction a generalizing k with
  | bot => exact Tree.bot_le _
  | top => exact absurd (by simp) (ha [])
  | node a ih =>
    rw [height_node] at hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [toTree_node, full_succ, Tree.node_le_node_iff]
    intro i
    exact ih i ((TopFree.node_iff _).mp ha i)
      ((Finset.le_sup (f := fun i => (a i).height) (Finset.mem_univ i)).trans (by omega))

/-- **The gadget lemma, part 2, finite witness.** `T_{h(t)+1}` is a gadget witness for every
top-free finite tree `t`. For `n ≥ 1` the height `h(t)` is the maximal length of a position of
`t`; at arity zero it is one for `f()`, and `T_{h(t)+1} = f()` in both readings. -/
theorem isWitness_full {a : FTree n} (ha : TopFree a.toTree) :
    TopFree.IsWitness a.toTree (full (a.height + 1)).toTree :=
  ⟨toTree_le_full ha (Nat.le_succ _), full_le_node _⟩

end DeciNSSE.FTree

namespace DeciENSSE
open DeciNSSE Core.Full

variable {n : ℕ}

namespace TopFree

/-! ## Witnesses in the three tree classes -/

/-- In the tree class `C`, every top-free tree has a gadget witness. -/
def HasWitnesses (C : Tree n → Prop) : Prop :=
  ∀ t, TopFree t → C t → ∃ y, C y ∧ IsWitness t y

/-- Arbitrary trees have the witness `Ω`. -/
theorem hasWitnesses_all : HasWitnesses (fun _ : Tree n => True) :=
  fun _ ht _ => ⟨_, trivial, isWitness_allF ht⟩

/-- Regular trees have the witness `Ω`, the unfolding of a one-state graph. -/
theorem hasWitnesses_reg : HasWitnesses fun t : Tree n => ∃ g : RGraph n, g.unfold = t :=
  fun _ ht _ => ⟨_, ⟨_, rfl⟩, isWitness_allF ht⟩

/-- Finite trees have the witness `T_{h(t)+1}`. -/
theorem hasWitnesses_fin : HasWitnesses fun t : Tree n => ∃ a : FTree n, a.toTree = t := by
  rintro _ ht ⟨a, rfl⟩
  exact ⟨_, ⟨_, rfl⟩, FTree.isWitness_full ht⟩

/-! ## The translation -/

variable {X Z V : Type*}

/-- The gadget `v ≤ y ∧ y ≤ f(y, …, y)` on `v`, with witness variable `y`. -/
def gadget (v y : V) : List (LitT n V) := [.le v y, .lef y fun _ => y]

/-- The antecedent `φ♮` over `X ⊕ X`: `φ` on the left copy, and a gadget from every listed
`x` to its right copy. -/
def gadgetAnte (xs : List X) (φ : List (LitT n X)) : List (LitT n (X ⊕ X)) :=
  φ.map (LitT.map .inl) ++ xs.flatMap fun x => gadget (.inl x) (.inr x)

/-- The consequent `ψ♮` over the visible `X ⊕ X` and the hidden `Z ⊕ Z`: `ψ` on the left
copies, and a gadget from every listed hidden `z` to its right copy. -/
def gadgetCons (zs : List Z) (ψ : List (LitT n (X ⊕ Z))) :
    List (LitT n ((X ⊕ X) ⊕ (Z ⊕ Z))) :=
  ψ.map (LitT.map (Sum.map .inl .inl)) ++
    zs.flatMap fun z => gadget (.inr (.inl z)) (.inr (.inr z))

/-- The translation adds two literals for every visible variable. -/
@[simp] theorem length_gadgetAnte (xs : List X) (φ : List (LitT n X)) :
    (gadgetAnte xs φ).length = φ.length + 2 * xs.length := by
  simp [gadgetAnte, gadget, List.length_flatMap, mul_comm]

/-- The translation adds two literals for every hidden variable. -/
@[simp] theorem length_gadgetCons (zs : List Z) (ψ : List (LitT n (X ⊕ Z))) :
    (gadgetCons zs ψ).length = ψ.length + 2 * zs.length := by
  simp [gadgetCons, gadget, List.length_flatMap, mul_comm]

/-- A gadget holds when its witness variable holds a gadget witness. -/
@[simp] theorem satT_gadget (ρ : V → Tree n) (v y : V) :
    SatT (fun _ => false) ρ (gadget v y) ↔ IsWitness (ρ v) (ρ y) := by
  simp [gadget, SatT, HoldsT, IsWitness, Function.comp_def]

/-- Satisfaction of `φ♮` when every visible variable is listed. -/
theorem satT_gadgetAnte {xs : List X} (hxs : ∀ x, x ∈ xs) (φ : List (LitT n X))
    (ρ : X ⊕ X → Tree n) :
    SatT (fun _ => false) ρ (gadgetAnte xs φ) ↔
      SatT (fun _ => false) (ρ ∘ .inl) φ ∧ ∀ x, IsWitness (ρ (.inl x)) (ρ (.inr x)) := by
  simp [gadgetAnte, hxs]

/-- Satisfaction of `ψ♮` when every hidden variable is listed. -/
theorem satT_gadgetCons {zs : List Z} (hzs : ∀ z, z ∈ zs) (ψ : List (LitT n (X ⊕ Z)))
    (ρ : X ⊕ X → Tree n) (σ : Z ⊕ Z → Tree n) :
    SatT (fun _ => false) (Sum.elim ρ σ) (gadgetCons zs ψ) ↔
      SatT (fun _ => false) (Sum.elim (ρ ∘ .inl) (σ ∘ .inl)) ψ ∧
        ∀ z, IsWitness (σ (.inl z)) (σ (.inr z)) := by
  simp [gadgetCons, hzs, Sum.elim_comp_map]

/-! ## The reduction -/

/-- **The gadget theorem.** In a tree class `C` in which every top-free tree has a gadget
witness, covariant existential entailment with all values top-free trees of `C` is covariant
existential entailment over `C` after adding the gadget on every visible and every hidden
variable. The systems may be arbitrary; over `{⊥, f}` they have no literal `x = ⊤`. -/
theorem existsEntailsTIn_iff_gadget {C : Tree n → Prop} (hC : HasWitnesses C)
    {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z} (hzs : ∀ z, z ∈ zs)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTIn (fun t => TopFree t ∧ C t) (fun _ => false) φ ψ ↔
      ExistsEntailsTIn C (fun _ => false) (gadgetAnte xs φ) (gadgetCons zs ψ) := by
  constructor
  · intro H ρ hρ hs
    obtain ⟨hφ, hw⟩ := (satT_gadgetAnte hxs φ ρ).mp hs
    obtain ⟨σ, hσ, hψ⟩ := H (ρ ∘ .inl) (fun x => ⟨of_isWitness (hw x), hρ _⟩) hφ
    choose y hyC hy using fun z => hC (σ z) (hσ z).1 (hσ z).2
    refine ⟨Sum.elim σ y, ?_, (satT_gadgetCons hzs ψ ρ _).mpr ⟨hψ, hy⟩⟩
    rintro (z | z)
    exacts [(hσ z).2, hyC z]
  · intro H ρ hρ hs
    choose y hyC hy using fun x => hC (ρ x) (hρ x).1 (hρ x).2
    obtain ⟨σ, hσ, hψ⟩ := H (Sum.elim ρ y) (by rintro (x | x); exacts [(hρ x).2, hyC x])
      ((satT_gadgetAnte hxs φ _).mpr ⟨hs, hy⟩)
    obtain ⟨hψ, hw⟩ := (satT_gadgetCons hzs ψ _ σ).mp hψ
    exact ⟨σ ∘ .inl, fun z => ⟨of_isWitness (hw z), hσ _⟩, hψ⟩

/-- The gadget theorem over arbitrary trees. -/
theorem existsEntailsT_iff_gadget {xs : List X} (hxs : ∀ x, x ∈ xs)
    {zs : List Z} (hzs : ∀ z, z ∈ zs) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTIn TopFree (fun _ => false) φ ψ ↔
      ExistsEntailsT (fun _ => false) (gadgetAnte xs φ) (gadgetCons zs ψ) := by
  have h := existsEntailsTIn_iff_gadget hasWitnesses_all hxs hzs φ ψ
  simp only [and_true] at h
  exact h

/-- The gadget theorem over regular trees. -/
theorem existsEntailsTReg_iff_gadget {xs : List X} (hxs : ∀ x, x ∈ xs)
    {zs : List Z} (hzs : ∀ z, z ∈ zs) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTIn (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t) (fun _ => false)
        φ ψ ↔
      ExistsEntailsTReg (fun _ => false) (gadgetAnte xs φ) (gadgetCons zs ψ) :=
  (existsEntailsTIn_iff_gadget hasWitnesses_reg hxs hzs φ ψ).trans
    (existsEntailsTReg_iff _ _ _).symm

/-- The gadget theorem over finite trees. -/
theorem existsEntailsTFin_iff_gadget {xs : List X} (hxs : ∀ x, x ∈ xs)
    {zs : List Z} (hzs : ∀ z, z ∈ zs) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTIn (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t) (fun _ => false)
        φ ψ ↔
      ExistsEntailsTFin (fun _ => false) (gadgetAnte xs φ) (gadgetCons zs ψ) :=
  (existsEntailsTIn_iff_gadget hasWitnesses_fin hxs hzs φ ψ).trans
    (existsEntailsTFin_iff _ _ _).symm

/-! ## Constructor positions

On top-free trees the covariant order is inclusion of constructor positions. -/

/-- Inclusion of constructor positions gives the covariant order below a top-free tree. -/
theorem le_of_constructor_subset {t u : Tree n} (ht : TopFree t)
    (h : ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f) : t ≤ u := by
  intro w a b ha hb
  cases a with
  | bot => exact Sym.bot_le _
  | top => exact False.elim (ht w ha)
  | f =>
    have : b = Sym.f := Option.some.inj (hb.symm.trans (h w ha))
    subst b; exact le_rfl

/-- Below a top-free tree, every constructor position is a constructor position of the upper
tree. -/
theorem constructor_subset_of_le {t u : Tree n} (hu : TopFree u) (h : t ≤ u) :
    ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro ht
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    have he := h [] Sym.f b ht hb
    cases b with
    | bot => simp at he
    | f => exact hb
    | top => exact False.elim (hu [] hb)
  | append_singleton w i ih =>
    intro ht
    have htf : t.fn w = some Sym.f := (t.child_isSome_iff w i).mp (by simp [ht])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((u.child_isSome_iff w i).mpr (ih htf))
    have he := h (w ++ [i]) Sym.f b ht hb
    cases b with
    | bot => simp at he
    | f => exact hb
    | top => exact False.elim (hu _ hb)

/-- On top-free trees the covariant order is inclusion of constructor positions. -/
theorem le_iff_constructor_subset {t u : Tree n} (ht : TopFree t) (hu : TopFree u) :
    t ≤ u ↔ ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f :=
  ⟨constructor_subset_of_le hu, le_of_constructor_subset ht⟩

end TopFree

end DeciENSSE
