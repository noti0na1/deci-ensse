import DeciNSSE.Constraints.Basic

/-! # Public existential entailment semantics

Visible variables are `V k`, hidden variables are `V h`, and consequents use
`V (k + h)`, with visible variables first. Variance `false` means covariance.

## Main declarations

- `ELit`, `EConstraint`, `ESat`: full-signature syntax and satisfaction.
- `BFLit`, `BFConstraint`, `BFSat`, `TopFree`: the bottom–constructor signature.
- `ExistsEntailsAny`, `ExistsEntailsAnyReg`, `ExistsEntailsAnyFin`: full signature.
- `ExistsEntails`, `ExistsEntailsReg`, `ExistsEntailsFin`: top-free semantics.
- `liftConstraint`, `query`: the ordinary subtype entailment interface.
-/

namespace DeciENSSE
open DeciNSSE

/-- Full-signature literals, including variable inequalities. -/
inductive ELit (n k : ℕ) where
  | le (x y : V k)
  | leF (x : V k) (a : Fin n → V k)
  | fLe (a : Fin n → V k) (x : V k)
  | eqBot (x : V k)
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
def ExistsEntailsAny {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ, ESat c ρ φ → ∃ σ : V h → Tree n, ESat c (join ρ σ) ψ

/-- Every regular visible solution has a regular hidden extension. -/
def ExistsEntailsAnyReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → RGraph n, ESat c (RGraph.unfold ∘ ρ) φ →
    ∃ σ : V h → RGraph n, ESat c (join (RGraph.unfold ∘ ρ) (RGraph.unfold ∘ σ)) ψ

/-- Every finite visible solution has a finite hidden extension. -/
def ExistsEntailsAnyFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ : V k → FTree n, ESat c (FTree.toTree ∘ ρ) φ →
    ∃ σ : V h → FTree n, ESat c (join (FTree.toTree ∘ ρ) (FTree.toTree ∘ σ)) ψ

/-- Embed a plain subtype literal. -/
def ofLit {n k : ℕ} : DeciNSSE.Lit n k → ELit n k
  | .leF x a => .leF x a
  | .fLe a x => .fLe a x
  | .eqBot x => .eqBot x
  | .eqTop x => .eqTop x

/-- Embed a plain subtype conjunction. -/
def liftConstraint {n k : ℕ} (φ : Constraint n k) : EConstraint n k := φ.map ofLit

/-- A visible inequality with no hidden variables. -/
def query {n k : ℕ} (x y : V k) : EConstraint n (k + 0) :=
  [.le (Fin.castAdd 0 x) (Fin.castAdd 0 y)]

/-- Embedding a plain conjunction preserves satisfaction. -/
@[simp] theorem sat_lift {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n)
    (φ : Constraint n k) : ESat c ρ (liftConstraint φ) ↔ Sat c ρ φ := by
  have hl (l : DeciNSSE.Lit n k) : (ofLit l).holds c ρ ↔ l.holds c ρ := by
    cases l <;> rfl
  simp [ESat, liftConstraint, Sat, hl]

/-- A query holds exactly when its visible inequality holds. -/
@[simp] theorem sat_query {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n)
    (σ : V 0 → Tree n) (x y : V k) :
    ESat c (join ρ σ) (query x y) ↔ Tree.Le c (ρ x) (ρ y) := by
  simp only [ESat, query, List.mem_singleton, forall_eq, ELit.holds, join, Fin.addCases_left]

/-- Bottom–constructor literals, with no top constant. -/
inductive BFLit (n k : ℕ) where
  | le (x y : DeciNSSE.V k)
  | leF (x : DeciNSSE.V k) (a : Fin n → DeciNSSE.V k)
  | fLe (a : Fin n → DeciNSSE.V k) (x : DeciNSSE.V k)
  | eqBot (x : DeciNSSE.V k)
/-- A finite conjunction of bottom–constructor literals. -/
abbrev BFConstraint (n k : ℕ) := List (BFLit n k)

/-- Embed a bottom–constructor literal into the full syntax. -/
def BFLit.toELit {n k : ℕ} : BFLit n k → ELit n k
  | .le x y => .le x y
  | .leF x a => .leF x a
  | .fLe a x => .fLe a x
  | .eqBot x => .eqBot x

/-- No path carries a top label. -/
def TopFree {n : ℕ} (t : DeciNSSE.Tree n) : Prop :=
  ∀ w, t.fn w ≠ some DeciNSSE.Sym.top

/-- Covariant satisfaction of a bottom–constructor conjunction. -/
def BFSat {n k : ℕ} (ρ : DeciNSSE.V k → DeciNSSE.Tree n)
    (φ : BFConstraint n k) : Prop :=
  ESat (fun _ => false) ρ (φ.map BFLit.toELit)

/-- Every top-free visible solution has a top-free hidden extension. -/
def ExistsEntails {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ, (∀ x, TopFree (ρ x)) → BFSat ρ φ →
    ∃ σ : DeciNSSE.V h → DeciNSSE.Tree n,
      (∀ z, TopFree (σ z)) ∧ BFSat (join ρ σ) ψ

/-- Every top-free regular visible solution has a top-free regular extension. -/
def ExistsEntailsReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ : DeciNSSE.V k → DeciNSSE.RGraph n,
    (∀ x, TopFree (ρ x).unfold) → BFSat (DeciNSSE.RGraph.unfold ∘ ρ) φ →
    ∃ σ : DeciNSSE.V h → DeciNSSE.RGraph n,
      (∀ z, TopFree (σ z).unfold) ∧
      BFSat (join (DeciNSSE.RGraph.unfold ∘ ρ) (DeciNSSE.RGraph.unfold ∘ σ)) ψ

/-- Every top-free finite visible solution has a top-free finite extension. -/
def ExistsEntailsFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Prop :=
  ∀ ρ : DeciNSSE.V k → DeciNSSE.FTree n,
    (∀ x, TopFree (ρ x).toTree) → BFSat (DeciNSSE.FTree.toTree ∘ ρ) φ →
    ∃ σ : DeciNSSE.V h → DeciNSSE.FTree n,
      (∀ z, TopFree (σ z).toTree) ∧
      BFSat (join (DeciNSSE.FTree.toTree ∘ ρ) (DeciNSSE.FTree.toTree ∘ σ)) ψ


end DeciENSSE
