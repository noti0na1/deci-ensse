import DeciNSSE.Constraints.Basic

/-! # Public existential entailment semantics

Existential entailment `φ ⊨ ∃ z̄. ψ` holds when every solution of the antecedent `φ`
extends, by some choice of trees for the hidden variables `z̄`, to a solution of the
consequent `ψ`. The antecedent has `k` visible variables `V k`; the consequent has the
variables `V (k + h)`, the visible ones first (`Fin.castAdd h x`) and then the `h` hidden
ones (`Fin.natAdd k z`). Variance `false` means covariance.

There are two signatures. Over `{⊥, f, ⊤}` the constructor `f` has any variance
`c : Fin n → Bool`. Over `{⊥, f}` the constructor is covariant, the trees have no `⊤`
label, and both assignments range over top-free trees. Each signature has a semantics over
arbitrary trees, over regular trees (unfoldings of `RGraph n`) and over finite trees
(images of `FTree n`), with the visible and the hidden assignments in the same class.

Plain subtype entailment `φ ⊨ x ≤ y` is the instance with no hidden variables and the
consequent `x ≤ y`: `liftConstraint` embeds a plain conjunction, and `query` and `bfQuery`
are the consequent in the two signatures.

## Main declarations

- `ELit`, `EConstraint`, `ESat`, `join`: full-signature syntax and satisfaction.
- `ExistsEntails`, `ExistsEntailsReg`, `ExistsEntailsFin`: full-signature entailment.
- `BFLit`, `BFConstraint`, `TopFree`, `BFSat`: the bottom–constructor signature.
- `ExistsEntailsTopFree`, `ExistsEntailsTopFreeReg`, `ExistsEntailsTopFreeFin`:
  bottom–constructor entailment over top-free trees.
- `liftConstraint`, `query`, `sat_lift`, `sat_query`: plain entailment as a query.
- `bfQuery`, `bfSat_query`, `EntailsTopFree`, `EntailsTopFreeReg`, `EntailsTopFreeFin`:
  plain entailment over top-free trees.
-/

namespace DeciENSSE
open DeciNSSE

/-! ## The full signature -/

/-- Full-signature literals, including variable inequalities. -/
inductive ELit (n k : ℕ) where
  /-- The variable inequality `x ≤ y`. -/
  | le (x y : V k)
  /-- The upper bound `x ≤ f(a)`. -/
  | leF (x : V k) (a : Fin n → V k)
  /-- The lower bound `f(a) ≤ x`. -/
  | fLe (a : Fin n → V k) (x : V k)
  /-- The equation `x = ⊥`. -/
  | eqBot (x : V k)
  /-- The equation `x = ⊤`. -/
  | eqTop (x : V k)

/-- A finite conjunction of full-signature literals. -/
abbrev EConstraint (n k : ℕ) := List (ELit n k)

/-- Interpret a literal under a tree assignment and variance. -/
def ELit.holds {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n) : ELit n k → Prop
  | .le x y => Tree.Le c (ρ x) (ρ y)
  | .leF x a => Tree.Le c (ρ x) (DeciNSSE.Tree.node (ρ ∘ a))
  | .fLe a x => Tree.Le c (DeciNSSE.Tree.node (ρ ∘ a)) (ρ x)
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- Every literal in the conjunction holds. -/
def ESat {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n)
    (φ : EConstraint n k) : Prop := ∀ l ∈ φ, l.holds c ρ

/-- Join visible and hidden assignments in that order. -/
def join {k h : ℕ} {A : Type*} (ρ : V k → A) (σ : V h → A) : V (k + h) → A :=
  Fin.addCases ρ σ

/-- Every visible solution extends to a solution over arbitrary trees. -/
def ExistsEntails {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ, ESat c ρ φ → ∃ σ : V h → Tree n, ESat c (join ρ σ) ψ

/-- Every regular visible solution has a regular hidden extension. -/
def ExistsEntailsReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → RGraph n, ESat c (RGraph.unfold ∘ ρ) φ →
    ∃ σ : V h → RGraph n, ESat c (join (RGraph.unfold ∘ ρ) (RGraph.unfold ∘ σ)) ψ

/-- Every finite visible solution has a finite hidden extension. -/
def ExistsEntailsFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → FTree n, ESat c (FTree.toTree ∘ ρ) φ →
    ∃ σ : V h → FTree n, ESat c (join (FTree.toTree ∘ ρ) (FTree.toTree ∘ σ)) ψ

/-! ## The bottom–constructor signature -/

/-- Bottom–constructor literals, with no top constant. -/
inductive BFLit (n k : ℕ) where
  /-- The variable inequality `x ≤ y`. -/
  | le (x y : V k)
  /-- The upper bound `x ≤ f(a)`. -/
  | leF (x : V k) (a : Fin n → V k)
  /-- The lower bound `f(a) ≤ x`. -/
  | fLe (a : Fin n → V k) (x : V k)
  /-- The equation `x = ⊥`. -/
  | eqBot (x : V k)

/-- A finite conjunction of bottom–constructor literals. -/
abbrev BFConstraint (n k : ℕ) := List (BFLit n k)

/-- Embed a bottom–constructor literal into the full syntax. -/
def BFLit.toELit {n k : ℕ} : BFLit n k → ELit n k
  | .le x y => .le x y
  | .leF x a => .leF x a
  | .fLe a x => .fLe a x
  | .eqBot x => .eqBot x

/-- No path carries a top label. -/
def TopFree {n : ℕ} (t : Tree n) : Prop :=
  ∀ w, t.fn w ≠ some Sym.top

/-- Covariant satisfaction of a bottom–constructor conjunction. -/
def BFSat {n k : ℕ} (ρ : V k → Tree n) (φ : BFConstraint n k) : Prop :=
  ESat (fun _ => false) ρ (φ.map BFLit.toELit)

/-- Every top-free visible solution has a top-free hidden extension. -/
def ExistsEntailsTopFree {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ, (∀ x, TopFree (ρ x)) → BFSat ρ φ →
    ∃ σ : V h → Tree n, (∀ z, TopFree (σ z)) ∧ BFSat (join ρ σ) ψ

/-- Every top-free regular visible solution has a top-free regular extension. -/
def ExistsEntailsTopFreeReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → RGraph n,
    (∀ x, TopFree (ρ x).unfold) → BFSat (RGraph.unfold ∘ ρ) φ →
    ∃ σ : V h → RGraph n,
      (∀ z, TopFree (σ z).unfold) ∧ BFSat (join (RGraph.unfold ∘ ρ) (RGraph.unfold ∘ σ)) ψ

/-- Every top-free finite visible solution has a top-free finite extension. -/
def ExistsEntailsTopFreeFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → FTree n,
    (∀ x, TopFree (ρ x).toTree) → BFSat (FTree.toTree ∘ ρ) φ →
    ∃ σ : V h → FTree n,
      (∀ z, TopFree (σ z).toTree) ∧ BFSat (join (FTree.toTree ∘ ρ) (FTree.toTree ∘ σ)) ψ

/-! ## Plain entailment as a query -/

/-- Embed a plain subtype literal. -/
def _root_.DeciNSSE.Lit.toELit {n k : ℕ} : Lit n k → ELit n k
  | .leF x a => .leF x a
  | .fLe a x => .fLe a x
  | .eqBot x => .eqBot x
  | .eqTop x => .eqTop x

/-- Embed a plain subtype conjunction. -/
def liftConstraint {n k : ℕ} (φ : Constraint n k) : EConstraint n k := φ.map Lit.toELit

/-- A visible inequality with no hidden variables. -/
def query {n k : ℕ} (x y : V k) : EConstraint n (k + 0) :=
  [.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]

/-- Embedding a plain conjunction preserves satisfaction. -/
@[simp] theorem sat_lift {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n)
    (φ : Constraint n k) : ESat c ρ (liftConstraint φ) ↔ Sat c ρ φ := by
  have hl (l : Lit n k) : (Lit.toELit l).holds c ρ ↔ l.holds c ρ := by
    cases l <;> rfl
  simp [ESat, liftConstraint, Sat, hl]

/-- A query holds exactly when its visible inequality holds. -/
@[simp] theorem sat_query {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n)
    (σ : V 0 → Tree n) (x y : V k) :
    ESat c (join ρ σ) (query x y) ↔ Tree.Le c (ρ x) (ρ y) := by
  simp only [ESat, query, List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left]

/-- A bottom–constructor visible inequality with no hidden variables. -/
def bfQuery {n k : ℕ} (x y : V k) : BFConstraint n (k + 0) :=
  [.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]

/-- A bottom–constructor query holds exactly when its covariant visible inequality holds. -/
@[simp] theorem bfSat_query {n k : ℕ} (ρ : V k → Tree n) (σ : V 0 → Tree n) (x y : V k) :
    BFSat (join ρ σ) (bfQuery x y) ↔ Tree.Le (fun _ => false) (ρ x) (ρ y) := by
  simp only [BFSat, bfQuery, List.map_cons, List.map_nil, BFLit.toELit, ESat,
    List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left]

/-- Covariant subtype entailment over top-free trees. -/
def EntailsTopFree {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ, (∀ v, TopFree (ρ v)) → BFSat ρ φ → Tree.Le (fun _ => false) (ρ x) (ρ y)

/-- Covariant subtype entailment over top-free regular trees. -/
def EntailsTopFreeReg {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ : V k → RGraph n,
    (∀ v, TopFree (ρ v).unfold) → BFSat (RGraph.unfold ∘ ρ) φ →
    Tree.Le (fun _ => false) (ρ x).unfold (ρ y).unfold

/-- Covariant subtype entailment over top-free finite trees. -/
def EntailsTopFreeFin {n k : ℕ} (φ : BFConstraint n k) (x y : V k) : Prop :=
  ∀ ρ : V k → FTree n,
    (∀ v, TopFree (ρ v).toTree) → BFSat (FTree.toTree ∘ ρ) φ →
    Tree.Le (fun _ => false) (ρ x).toTree (ρ y).toTree

end DeciENSSE
