import DeciNSSE.Constraints.Basic

/-! # Existential entailment with top and variance

Flat conjunctions over arbitrary visible and hidden carriers, interpreted over
arbitrary trees, regular graph unfoldings, or finite terms.

## Main declarations

- `LitT`, `HoldsT`, `SatT`: syntax and satisfaction.
- `ExistsEntailsTIn`: entailment with both tuples restricted to a tree class.
- `ExistsEntailsT`, `ExistsEntailsTReg`, `ExistsEntailsTFin`: the three semantics.
- `existsEntailsT_ofLitN_le_iff`: ordinary entailment as a special case.
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

/-- Flat literals with variable inequalities, constructor bounds, and both extremes. -/
inductive LitT (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fle (a : Fin n → V) (u : V)
  | lef (u : V) (a : Fin n → V)
  | bot (u : V)
  | top (u : V)
  deriving DecidableEq

/-- Rename every variable in a literal. -/
def LitT.map {V W : Type*} (f : V → W) : LitT n V → LitT n W
  | .le u v => .le (f u) (f v)
  | .fle a u => .fle (f ∘ a) (f u)
  | .lef u a => .lef (f u) (f ∘ a)
  | .bot u => .bot (f u)
  | .top u => .top (f u)

/-- Interpret a literal using the given variance. -/
def HoldsT {V : Type*} (c : Fin n → Bool) (ρ : V → Tree n) : LitT n V → Prop
  | .le u v => Tree.Le c (ρ u) (ρ v)
  | .fle a u => Tree.Le c (DeciNSSE.Tree.node (ρ ∘ a)) (ρ u)
  | .lef u a => Tree.Le c (ρ u) (DeciNSSE.Tree.node (ρ ∘ a))
  | .bot u => ρ u = Tree.bot
  | .top u => ρ u = Tree.top

/-- Renaming literals is equivalent to precomposing assignments. -/
@[simp] theorem holdsT_map {V W : Type*} (c : Fin n → Bool)
    (f : V → W) (ρ : W → Tree n) (l : LitT n V) :
    HoldsT c ρ (l.map f) ↔ HoldsT c (ρ ∘ f) l := by cases l <;> rfl

/-- Every literal in the conjunction holds. -/
def SatT {V : Type*} (c : Fin n → Bool) (ρ : V → Tree n)
    (χ : List (LitT n V)) : Prop := ∀ l ∈ χ, HoldsT c ρ l

/-- Class restrictions apply to both the visible tuple and its extension. -/
def ExistsEntailsTIn {X Z : Type*} (C : Tree n → Prop) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ ρ, (∀ x, C (ρ x)) → SatT c ρ φ →
    ∃ σ, (∀ z, C (σ z)) ∧ SatT c (Sum.elim ρ σ) ψ

/-- Every visible solution has a hidden extension. -/
def ExistsEntailsT {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ExistsEntailsTIn (fun _ => True) c φ ψ

/-- Both visible and hidden assignments are regular graph presentations. -/
def ExistsEntailsTReg {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ ρ : X → RGraph n, SatT c (RGraph.unfold ∘ ρ) φ →
    ∃ σ : Z → RGraph n,
      SatT c (Sum.elim (RGraph.unfold ∘ ρ) (RGraph.unfold ∘ σ)) ψ

/-- Both visible and hidden assignments are finite terms. -/
def ExistsEntailsTFin {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ ρ : X → FTree n, SatT c (FTree.toTree ∘ ρ) φ →
    ∃ σ : Z → FTree n,
      SatT c (Sum.elim (FTree.toTree ∘ ρ) (FTree.toTree ∘ σ)) ψ

/-- Quantifying presentations is equivalent to restricting to their image. -/
theorem existsEntailsTIn_range_iff {X Z D : Type*} (f : D → Tree n)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTIn (fun t => ∃ d, f d = t) c φ ψ ↔
      ∀ ρ : X → D, SatT c (f ∘ ρ) φ →
        ∃ σ : Z → D, SatT c (Sum.elim (f ∘ ρ) (f ∘ σ)) ψ := by
  classical
  constructor
  · intro h ρ hρ
    obtain ⟨σ, hσ, hs⟩ := h (f ∘ ρ) (fun x => ⟨ρ x, rfl⟩) hρ
    choose τ hτ using hσ
    refine ⟨τ, ?_⟩
    have : f ∘ τ = σ := funext hτ
    simpa [this] using hs
  · intro h ρ hρ hs
    choose τ hτ using hρ
    have he : f ∘ τ = ρ := funext hτ
    obtain ⟨σ, hσ⟩ := h τ (he.symm ▸ hs)
    exact ⟨f ∘ σ, fun z => ⟨σ z, rfl⟩, he ▸ hσ⟩

/-- Regular presentations and their image define the same entailment. -/
theorem existsEntailsTReg_iff {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTReg c φ ψ ↔
      ExistsEntailsTIn (fun t => ∃ g : RGraph n, g.unfold = t) c φ ψ :=
  (existsEntailsTIn_range_iff _ _ _ _).symm

/-- Finite presentations and their image define the same entailment. -/
theorem existsEntailsTFin_iff {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTFin c φ ψ ↔
      ExistsEntailsTIn (fun t => ∃ a : FTree n, a.toTree = t) c φ ψ :=
  (existsEntailsTIn_range_iff _ _ _ _).symm

/-- A visible inequality is the special case of existential entailment. -/
theorem existsEntailsT_le_iff {X Z : Type*} (c : Fin n → Bool)
    (φ : List (LitT n X)) (x y : X) :
    ExistsEntailsT c φ [(.le (.inl x) (.inl y) : LitT n (X ⊕ Z))] ↔
      ∀ ρ, SatT c ρ φ → Tree.Le c (ρ x) (ρ y) := by
  constructor
  · intro h ρ hs
    obtain ⟨σ, _, hσ⟩ := h ρ (fun _ => trivial) hs
    exact hσ (.le (.inl x) (.inl y)) (by simp)
  · intro h ρ _ hs
    exact ⟨fun _ => Tree.bot, fun _ => trivial, by simpa [SatT, HoldsT] using h ρ hs⟩

/-- Embed the existing plain-constraint language (which has no variable inequality). -/
def ofLitN {k : ℕ} : Lit n k → LitT n (Fin k)
  | .leF u a => .lef u a
  | .fLe a u => .fle a u
  | .eqBot u => .bot u
  | .eqTop u => .top u

/-- Embedding a plain literal preserves its meaning. -/
@[simp] theorem holdsT_ofLitN {k : ℕ} (c : Fin n → Bool)
    (ρ : Fin k → Tree n) (l : Lit n k) :
    HoldsT c ρ (ofLitN l) ↔ Lit.holds c ρ l := by
  cases l <;> rfl

/-- Embedding a plain conjunction preserves satisfaction. -/
@[simp] theorem satT_ofLitN {k : ℕ} (c : Fin n → Bool)
    (ρ : Fin k → Tree n) (φ : Constraint n k) :
    SatT c ρ (φ.map ofLitN) ↔ Sat c ρ φ := by
  simp [SatT, Sat]

/-- Plain subtype entailment is existential entailment of a visible inequality. -/
theorem existsEntailsT_ofLitN_le_iff {k : ℕ} {Z : Type*} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : Fin k) :
    ExistsEntailsT c (φ.map ofLitN)
      [(.le (.inl x) (.inl y) : LitT n (Fin k ⊕ Z))] ↔ Entails c φ x y := by
  simp [existsEntailsT_le_iff, Entails]

end DeciENSSE.Core.Full
