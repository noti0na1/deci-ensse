import DeciNSSE.Constraints.Basic

/-! # The three-element nullary domain

Every nullary tree is a single label. Finite terms and regular graphs cover
this domain, and subtype comparison is the label order.

## Main declarations

- `treeEquiv`: nullary trees correspond to labels.
- `treeLe_zero_iff`: comparison is root-label comparison.
- `toTree_zero_surjective`, `unfold_zero_surjective`: both presentations cover all trees.
-/

namespace DeciENSSE.Support.Nullary
open DeciNSSE DeciNSSE.Tree

/-- The only variance vector at arity zero is the covariant one. -/
theorem variance_zero (c : Fin 0 → Bool) : c = fun _ => false :=
  funext fun i => i.elim0

/-- Every constructor tree of arity zero is `f()`. -/
theorem node_eq_f (a : Fin 0 → Tree 0) : node a = node Fin.elim0 := by
  congr 1
  funext i
  exact i.elim0

/-- **Classification of `Tree 0`.** -/
theorem tree_zero_cases (t : Tree 0) : t = bot ∨ t = top ∨ t = node Fin.elim0 := by
  rcases t.eq_bot_or_eq_top_or_node with h | h | ⟨a, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (node_eq_f a))

/-- A tree of arity zero is determined by its root label. -/
theorem tree_zero_ext {t u : Tree 0} (h : t.fn [] = u.fn []) : t = u := by
  apply Tree.ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => exact i.elim0

/-- The tree carrying a given root label. -/
def ofSym : Sym → Tree 0
  | .bot => bot
  | .f => node Fin.elim0
  | .top => top

/-- The root label of a tree (`getD` only to stay total; roots always exist). -/
def toSym (t : Tree 0) : Sym := (t.fn []).getD Sym.bot

/-- The bottom label decodes to bottom. -/
@[simp] theorem ofSym_bot : ofSym Sym.bot = bot := rfl
/-- The constructor label decodes to the nullary constructor. -/
@[simp] theorem ofSym_f : ofSym Sym.f = node Fin.elim0 := rfl
/-- The top label decodes to top. -/
@[simp] theorem ofSym_top : ofSym Sym.top = top := rfl

/-- Decoding preserves the root label. -/
@[simp] theorem ofSym_fn_nil (s : Sym) : (ofSym s).fn [] = some s := by
  cases s <;> rfl

/-- Bottom has the bottom label. -/
@[simp] theorem toSym_bot : toSym (bot : Tree 0) = Sym.bot := rfl
/-- Top has the top label. -/
@[simp] theorem toSym_top : toSym (top : Tree 0) = Sym.top := rfl
/-- A constructor has the constructor label. -/
@[simp] theorem toSym_node (a : Fin 0 → Tree 0) : toSym (node a) = Sym.f := rfl

/-- Encoding after decoding is the identity. -/
@[simp] theorem toSym_ofSym (s : Sym) : toSym (ofSym s) = s := by
  cases s <;> rfl

/-- Decoding after encoding is the identity. -/
@[simp] theorem ofSym_toSym (t : Tree 0) : ofSym (toSym t) = t := by
  rcases tree_zero_cases t with rfl | rfl | rfl <;> rfl

/-- Distinct labels give distinct trees. -/
theorem ofSym_injective : Function.Injective ofSym := fun a b h => by
  simpa using congrArg toSym h

/-- Equality of decoded trees is equality of labels. -/
@[simp] theorem ofSym_inj {a b : Sym} : ofSym a = ofSym b ↔ a = b :=
  ofSym_injective.eq_iff

/-- `Tree 0` is the three-element chain of labels. -/
def treeEquiv : Tree 0 ≃ Sym where
  toFun := toSym
  invFun := ofSym
  left_inv := ofSym_toSym
  right_inv := toSym_ofSym

/-- `Tree.Le c` on labeled trees is the order of `Sym`. -/
@[simp] theorem treeLe_ofSym_iff (c : Fin 0 → Bool) (a b : Sym) :
    Tree.Le c (ofSym a) (ofSym b) ↔ a ≤ b := by
  rw [variance_zero c, treeLe_false_iff_le]
  cases a <;> cases b <;> simp

/-- **`Tree.Le c` on `Tree 0` is the chain order on root labels.** -/
theorem treeLe_zero_iff (c : Fin 0 → Bool) (t u : Tree 0) :
    Tree.Le c t u ↔ toSym t ≤ toSym u := by
  rw [← treeLe_ofSym_iff c, ofSym_toSym, ofSym_toSym]

/-- The finite tree carrying a given label. -/
def fOfSym : Sym → FTree 0
  | .bot => .bot
  | .f => .node Fin.elim0
  | .top => .top

/-- The finite presentation decodes to the same tree. -/
@[simp] theorem fOfSym_toTree (s : Sym) : (fOfSym s).toTree = ofSym s := by
  cases s
  · rfl
  · show DeciNSSE.Tree.node _ = DeciNSSE.Tree.node _
    exact node_eq_f _
  · rfl

/-- At arity zero every tree is finite. -/
theorem toTree_zero_surjective : Function.Surjective (@FTree.toTree 0) :=
  fun t => ⟨fOfSym (toSym t), by simp⟩

/-- The unfolding of a nullary graph is fixed by the root label. -/
theorem rGraph_unfold_zero (g : RGraph 0) : g.unfold = ofSym (g.label g.root) :=
  tree_zero_ext (by rw [RGraph.unfold_root, ofSym_fn_nil])

/-- The one-state graph carrying a given label. -/
def gOfSym (s : Sym) : RGraph 0 where
  size := 1
  root := 0
  label := fun _ => s
  child := fun _ i => i.elim0

/-- The one-state graph decodes to the same tree. -/
@[simp] theorem gOfSym_unfold (s : Sym) : (gOfSym s).unfold = ofSym s :=
  rGraph_unfold_zero _

/-- At arity zero every tree is regular. -/
theorem unfold_zero_surjective : Function.Surjective (@RGraph.unfold 0) :=
  fun t => ⟨gOfSym (toSym t), by simp⟩

end DeciENSSE.Support.Nullary
