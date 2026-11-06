import Mathlib.Algebra.BigOperators.Fin
import DeciENSSE.TopFree
import DeciNSSE.Semantics.Characterization

/-! # Type expressions and constraints between them

The flat systems of `DeciENSSE.Semantics` relate variables. This module defines constraints
between arbitrary finite *type expressions*: inequalities `e ≤ e'` and equalities `e = e'`
between expressions built from variables, `⊥`, the constructor `f` of arity `n` and, over
`{⊥, f, ⊤}`, `⊤`; and existential entailment between such systems in a tree class.
`DeciENSSE.Flattening` reduces it to existential entailment between flat systems and decides
it.

Variables range over arbitrary types: the antecedent is over the visible variables `X` and
the consequent over `X ⊕ Z`, with the hidden variables `Z`. A tree class is a predicate on
trees; the regular trees are the unfoldings of finite graphs and the finite trees the values
of finite terms, as in `DeciENSSE.Semantics`.

## Main declarations

- `Term`, `BFTerm`: type expressions over `{⊥, f, ⊤}` and over `{⊥, f}`; `Term.eval`,
  `Term.map`, `BFTerm.toTerm`.
- `TermClosed`, `BFTermClosed`: tree classes closed under the constants and the constructor;
  `termClosed_all`, `termClosed_reg`, `termClosed_fin`, `TermClosed.topFree`,
  `bfTermClosed_topFree`.
- `TermLit`, `TermSystem`, `BFTermSystem`, `TermSat`: constraints between expressions.
- `ExistsEntailsTermIn`: existential entailment in a tree class, with the instances
  `ExistsEntailsTerm`, `ExistsEntailsTermReg`, `ExistsEntailsTermFin` over `{⊥, f, ⊤}` and
  `ExistsEntailsTermTopFree`, `ExistsEntailsTermTopFreeReg`, `ExistsEntailsTermTopFreeFin`
  over `{⊥, f}`.
-/

namespace DeciENSSE
open DeciNSSE Characterization

variable {n : ℕ}

/-! ## Type expressions -/

/-- Type expressions over `{⊥, f, ⊤}` with variables in `V`. -/
inductive Term (n : ℕ) (V : Type*) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constant `⊤`. -/
  | top
  /-- The constructor `f(e₀, …, e_{n-1})`. -/
  | node (a : Fin n → Term n V)

/-- Type expressions over `{⊥, f}`, with variables in `V`. -/
inductive BFTerm (n : ℕ) (V : Type*) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constructor `f(e₀, …, e_{n-1})`. -/
  | node (a : Fin n → BFTerm n V)

namespace Term

variable {V W : Type*}

/-- The value of an expression when its variables have the values `ρ`. -/
def eval (ρ : V → Tree n) : Term n V → Tree n
  | var v => ρ v
  | bot => Tree.bot
  | top => Tree.top
  | node a => DeciNSSE.Tree.node fun i => (a i).eval ρ

@[simp] theorem eval_var (ρ : V → Tree n) (v : V) : (var v : Term n V).eval ρ = ρ v := rfl
@[simp] theorem eval_bot (ρ : V → Tree n) : (bot : Term n V).eval ρ = Tree.bot := rfl
@[simp] theorem eval_top (ρ : V → Tree n) : (top : Term n V).eval ρ = Tree.top := rfl
@[simp] theorem eval_node (ρ : V → Tree n) (a : Fin n → Term n V) :
    (node a).eval ρ = DeciNSSE.Tree.node fun i => (a i).eval ρ := rfl

/-- Rename the variables of an expression. -/
def map (f : V → W) : Term n V → Term n W
  | var v => var (f v)
  | bot => bot
  | top => top
  | node a => node fun i => (a i).map f

/-- Renaming the variables precomposes the assignment. -/
@[simp] theorem eval_map (f : V → W) (ρ : W → Tree n) (e : Term n V) :
    (e.map f).eval ρ = e.eval (ρ ∘ f) := by
  induction e with
  | var v => rfl
  | bot => rfl
  | top => rfl
  | node a ih => simp only [map, eval_node, ih]

/-- Equality of expressions is decidable. -/
protected def decEq [DecidableEq V] : (s t : Term n V) → Decidable (s = t)
  | var x, var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | var _, bot | var _, top | var _, node _ | bot, var _ | bot, top | bot, node _
  | top, var _ | top, bot | top, node _ | node _, var _ | node _, bot | node _, top =>
    isFalse fun e => by cases e
  | bot, bot => isTrue rfl
  | top, top => isTrue rfl
  | node a, node b =>
    letI : ∀ i, Decidable (a i = b i) := fun i => Term.decEq (a i) (b i)
    decidable_of_iff (∀ i, a i = b i)
      ⟨fun h => congrArg node (funext h), fun h => by cases h; exact fun _ => rfl⟩

instance [DecidableEq V] : DecidableEq (Term n V) := Term.decEq

/-- The number of symbols of an expression. -/
def size : Term n V → ℕ
  | var _ => 1
  | bot => 1
  | top => 1
  | node a => 1 + ∑ i, (a i).size

theorem size_pos (t : Term n V) : 0 < t.size := by
  cases t <;> simp [size]

/-- The nonvariable subexpressions of an expression, in prefix order and with repetitions. -/
def names : Term n V → List (Term n V)
  | var _ => []
  | bot => [bot]
  | top => [top]
  | node a => node a :: (List.finRange n).flatMap fun i => (a i).names

/-- The subexpressions of a child are subexpressions of the constructor expression. -/
theorem names_child_subset (a : Fin n → Term n V) (i : Fin n) :
    (a i).names ⊆ (node a).names :=
  fun _ he => List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, he⟩)

/-- The subexpressions of a subexpression are subexpressions. -/
theorem names_subset_of_mem {e t : Term n V} (h : e ∈ t.names) : e.names ⊆ t.names := by
  induction t with
  | var => simp [names] at h
  | bot => rw [List.mem_singleton.mp h]
  | top => rw [List.mem_singleton.mp h]
  | node a ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.Subset.refl _
    · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp h
      exact List.Subset.trans (ih i hi) (names_child_subset a i)

/-- A variable is not a subexpression in the sense of `names`. -/
theorem var_notMem_names (x : V) (t : Term n V) : var x ∉ t.names := by
  induction t with
  | var => simp [names]
  | bot => simp [names]
  | top => simp [names]
  | node a ih =>
    simp only [names, List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_finRange,
      true_and, false_or, not_exists]
    exact ih

/-- An expression has at most as many nonvariable subexpressions as symbols. -/
theorem length_names_le (t : Term n V) : t.names.length ≤ t.size := by
  induction t with
  | var => simp [names, size]
  | bot => simp [names, size]
  | top => simp [names, size]
  | node a ih =>
    simp only [names, size, List.length_cons, List.length_flatMap, Fin.sum_univ_def]
    have := List.sum_le_sum (l := List.finRange n) (f := fun i => (a i).names.length)
      (g := fun i => (a i).size) fun i _ => ih i
    omega

end Term

namespace BFTerm

variable {V W : Type*}

/-- An expression over `{⊥, f}` is an expression over `{⊥, f, ⊤}`. -/
def toTerm : BFTerm n V → Term n V
  | var v => .var v
  | bot => .bot
  | node a => .node fun i => (a i).toTerm

/-- Rename the variables of an expression. -/
def map (f : V → W) : BFTerm n V → BFTerm n W
  | var v => var (f v)
  | bot => bot
  | node a => node fun i => (a i).map f

/-- Renaming commutes with the embedding. -/
@[simp] theorem toTerm_map (f : V → W) (e : BFTerm n V) :
    (e.map f).toTerm = e.toTerm.map f := by
  induction e with
  | var v => rfl
  | bot => rfl
  | node a ih => simp only [map, toTerm, Term.map, ih]

/-- The subexpressions of an embedded expression are embedded expressions. -/
theorem exists_of_mem_names {e : Term n V} {t : BFTerm n V} (h : e ∈ t.toTerm.names) :
    ∃ b : BFTerm n V, b.toTerm = e := by
  induction t with
  | var => simp [toTerm, Term.names] at h
  | bot => exact ⟨bot, (List.mem_singleton.mp h).symm⟩
  | node a ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨node a, rfl⟩
    · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp h
      exact ih i hi

end BFTerm

/-! ## Tree classes closed under the constructors -/

/-- A tree class that contains `⊥` and `⊤` and is closed under the constructor. -/
structure TermClosed (C : Tree n → Prop) : Prop where
  bot : C Tree.bot
  top : C Tree.top
  node : ∀ a : Fin n → Tree n, (∀ i, C (a i)) → C (DeciNSSE.Tree.node a)

/-- A tree class that contains `⊥` and is closed under the constructor. -/
structure BFTermClosed (C : Tree n → Prop) : Prop where
  bot : C Tree.bot
  node : ∀ a : Fin n → Tree n, (∀ i, C (a i)) → C (DeciNSSE.Tree.node a)

/-- A class closed under the constructors contains the value of every expression at every
assignment into it. -/
theorem TermClosed.eval {C : Tree n → Prop} (hC : TermClosed C) {V : Type*} {ρ : V → Tree n}
    (hρ : ∀ v, C (ρ v)) (e : Term n V) : C (e.eval ρ) := by
  induction e with
  | var v => exact hρ v
  | bot => exact hC.bot
  | top => exact hC.top
  | node a ih => exact hC.node _ ih

/-- A class closed under `⊥` and the constructor contains the value of every expression over
`{⊥, f}` at every assignment into it. -/
theorem BFTermClosed.eval {C : Tree n → Prop} (hC : BFTermClosed C) {V : Type*}
    {ρ : V → Tree n} (hρ : ∀ v, C (ρ v)) (e : BFTerm n V) : C (e.toTerm.eval ρ) := by
  induction e with
  | var v => exact hρ v
  | bot => exact hC.bot
  | node a ih => exact hC.node _ ih

/-- The class of all trees. -/
theorem termClosed_all : TermClosed fun _ : Tree n => True := ⟨trivial, trivial, fun _ _ => trivial⟩

/-- The subtrees of `f(a₀, …, a_{n-1})` below the root are the subtrees of its children. -/
private theorem subtree_node_cons (a : Fin n → Tree n) (i : Fin n) (π : List (Fin n)) :
    (DeciNSSE.Tree.node a).subtree (i :: π) = (a i).subtree π := rfl

/-- The regular trees, the unfoldings of finite graphs. -/
theorem termClosed_reg : TermClosed fun t : Tree n => ∃ g : RGraph n, g.unfold = t := by
  have hfin (t : Tree n) (ht : t.fn [] ≠ some Sym.f) : (subtrees t).Finite := by
    refine (Set.finite_singleton t).subset ?_
    rintro u ⟨π, hπ⟩
    cases π with
    | nil => rw [subtree_nil] at hπ; exact (Option.some.inj hπ).symm
    | cons i π =>
      have := (Tree.subtree_isSome_iff t (i :: π)).mp (by simp [hπ])
      simp [Tree.fn_cons_eq_none_of_root_ne_f t ht] at this
  refine ⟨(unfold_range_iff _).mpr (hfin _ (by simp)),
    (unfold_range_iff _).mpr (hfin _ (by simp)), fun a ha => (unfold_range_iff _).mpr ?_⟩
  have hS i := (unfold_range_iff (a i)).mp (ha i)
  refine ((Set.finite_iUnion hS).insert (DeciNSSE.Tree.node a)).subset ?_
  rintro u ⟨π, hπ⟩
  cases π with
  | nil => rw [subtree_nil] at hπ; exact Or.inl (Option.some.inj hπ).symm
  | cons i π => exact Or.inr (Set.mem_iUnion.mpr ⟨i, π, by rwa [subtree_node_cons] at hπ⟩)

/-- The finite trees, the values of finite terms. -/
theorem termClosed_fin : TermClosed fun t : Tree n => ∃ a : FTree n, a.toTree = t := by
  refine ⟨⟨.bot, rfl⟩, ⟨.top, rfl⟩, fun a ha => ?_⟩
  choose b hb using ha
  exact ⟨.node b, by simp [hb]⟩

/-- The top-free trees of a class closed under the constructors are closed under `⊥` and the
constructor. -/
theorem TermClosed.topFree {C : Tree n → Prop} (hC : TermClosed C) :
    BFTermClosed fun t => TopFree t ∧ C t :=
  ⟨⟨TopFree.bot, hC.bot⟩, fun a ha =>
    ⟨(TopFree.node_iff a).mpr fun i => (ha i).1, hC.node a fun i => (ha i).2⟩⟩

/-- The top-free trees are closed under `⊥` and the constructor. -/
theorem bfTermClosed_topFree : BFTermClosed (TopFree : Tree n → Prop) :=
  ⟨TopFree.bot, fun a ha => (TopFree.node_iff a).mpr ha⟩

/-! ## Constraints between expressions -/

/-- A constraint between two expressions: an inequality `e ≤ e'` or an equality `e = e'`. -/
inductive TermLit (T : Type*) where
  /-- The inequality `e ≤ e'`. -/
  | le (e e' : T)
  /-- The equality `e = e'`. -/
  | eq (e e' : T)

/-- A finite conjunction of constraints between expressions over `{⊥, f, ⊤}`. -/
abbrev TermSystem (n : ℕ) (V : Type*) := List (TermLit (Term n V))

/-- A finite conjunction of constraints between expressions over `{⊥, f}`. -/
abbrev BFTermSystem (n : ℕ) (V : Type*) := List (TermLit (BFTerm n V))

namespace TermLit

variable {T T' V W : Type*}

/-- Map both sides of a constraint. -/
def map (f : T → T') : TermLit T → TermLit T'
  | le e e' => le (f e) (f e')
  | eq e e' => eq (f e) (f e')

theorem map_map {T'' : Type*} (f : T → T') (g : T' → T'') (l : TermLit T) :
    (l.map f).map g = l.map (g ∘ f) := by
  cases l <;> rfl

/-- A constraint holds under an assignment, with the order of the variance `c`. -/
def Holds (c : Fin n → Bool) (ρ : V → Tree n) : TermLit (Term n V) → Prop
  | le e e' => Tree.Le c (e.eval ρ) (e'.eval ρ)
  | eq e e' => e.eval ρ = e'.eval ρ

/-- Renaming the variables of a constraint precomposes the assignment. -/
@[simp] theorem holds_map (c : Fin n → Bool) (f : V → W) (ρ : W → Tree n)
    (l : TermLit (Term n V)) : (l.map (Term.map f)).Holds c ρ ↔ l.Holds c (ρ ∘ f) := by
  cases l <;> simp [map, Holds]

/-- The nonvariable subexpressions of both sides. -/
def names : TermLit (Term n V) → List (Term n V)
  | le e e' => e.names ++ e'.names
  | eq e e' => e.names ++ e'.names

/-- The number of symbols of both sides. -/
def size : TermLit (Term n V) → ℕ
  | le e e' => e.size + e'.size
  | eq e e' => e.size + e'.size

end TermLit

variable {V W X Y Z : Type*}

/-- Every constraint of the system holds. -/
def TermSat (c : Fin n → Bool) (ρ : V → Tree n) (φ : TermSystem n V) : Prop :=
  ∀ l ∈ φ, l.Holds c ρ

@[simp] theorem termSat_nil (c : Fin n → Bool) (ρ : V → Tree n) : TermSat c ρ [] := by
  simp [TermSat]

@[simp] theorem termSat_cons (c : Fin n → Bool) (ρ : V → Tree n) (l : TermLit (Term n V))
    (φ : TermSystem n V) : TermSat c ρ (l :: φ) ↔ l.Holds c ρ ∧ TermSat c ρ φ := by
  simp [TermSat]

@[simp] theorem termSat_append (c : Fin n → Bool) (ρ : V → Tree n) (φ ψ : TermSystem n V) :
    TermSat c ρ (φ ++ ψ) ↔ TermSat c ρ φ ∧ TermSat c ρ ψ := by
  simp [TermSat, or_imp, forall_and]

/-- Renaming the variables of a system precomposes the assignment. -/
@[simp] theorem termSat_map (c : Fin n → Bool) (f : V → W) (ρ : W → Tree n)
    (φ : TermSystem n V) :
    TermSat c ρ (φ.map (TermLit.map (Term.map f))) ↔ TermSat c (ρ ∘ f) φ := by
  simp [TermSat]

/-! ## Existential entailment between systems of expressions -/

/-- Existential entailment `φ ⊨ ∃ z̄. ψ` in the tree class `C`: every solution of `φ` with
values in `C` extends, by values in `C` for the hidden variables `Z`, to a solution of `ψ`. -/
def ExistsEntailsTermIn (C : Tree n → Prop) (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Prop :=
  ∀ ρ : X → Tree n, (∀ x, C (ρ x)) → TermSat c ρ φ →
    ∃ σ : Z → Tree n, (∀ z, C (σ z)) ∧ TermSat c (Sum.elim ρ σ) ψ

/-- Existential entailment over arbitrary trees. -/
def ExistsEntailsTerm (c : Fin n → Bool) (φ : TermSystem n X) (ψ : TermSystem n (X ⊕ Z)) :
    Prop :=
  ExistsEntailsTermIn (fun _ => True) c φ ψ

/-- Existential entailment over regular trees, the unfoldings of finite graphs. -/
def ExistsEntailsTermReg (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Prop :=
  ExistsEntailsTermIn (fun t => ∃ g : RGraph n, g.unfold = t) c φ ψ

/-- Existential entailment over finite trees. -/
def ExistsEntailsTermFin (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Prop :=
  ExistsEntailsTermIn (fun t => ∃ a : FTree n, a.toTree = t) c φ ψ

/-- Covariant existential entailment over top-free trees, for systems over `{⊥, f}`. -/
def ExistsEntailsTermTopFree (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) : Prop :=
  ExistsEntailsTermIn TopFree (fun _ => false) (φ.map (TermLit.map BFTerm.toTerm))
    (ψ.map (TermLit.map BFTerm.toTerm))

/-- Covariant existential entailment over top-free regular trees. -/
def ExistsEntailsTermTopFreeReg (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) :
    Prop :=
  ExistsEntailsTermIn (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t) (fun _ => false)
    (φ.map (TermLit.map BFTerm.toTerm)) (ψ.map (TermLit.map BFTerm.toTerm))

/-- Covariant existential entailment over top-free finite trees. -/
def ExistsEntailsTermTopFreeFin (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) :
    Prop :=
  ExistsEntailsTermIn (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t) (fun _ => false)
    (φ.map (TermLit.map BFTerm.toTerm)) (ψ.map (TermLit.map BFTerm.toTerm))

end DeciENSSE
