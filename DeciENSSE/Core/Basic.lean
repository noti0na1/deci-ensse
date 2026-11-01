import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ext

/-! # Trees and existential entailment over {⊥, fₙ}

Trees are prefix-closed sets of constructor positions. Literals and existential
entailment use arbitrary visible and hidden variable types.

## Main declarations

- `BFTreeN`
- `Lit`
- `Sat`
- `IsFiniteTree`
- `IsRegularTree`
- `ExistsEntailsIn`
- `ExistsEntails`
-/

namespace DeciENSSE.Core

variable {n : ℕ}

/-- Constructor positions, closed under taking prefixes. -/
@[ext] structure BFTreeN (n : ℕ) where
  /-- Positions occupied by constructor nodes. -/
  K : Set (List (Fin n))
  /-- Every prefix of a constructor position is also a constructor position. -/
  prefix_closed : ∀ u v, u ++ v ∈ K → u ∈ K

namespace BFTreeN

/-- The bottom tree has no constructor positions. -/
def bot : BFTreeN n := ⟨∅, by simp⟩

/-- A constructor root with the given children. -/
def node (a : Fin n → BFTreeN n) : BFTreeN n where
  K w := match w with
    | [] => True
    | i :: v => v ∈ (a i).K
  prefix_closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons i u => exact (a i).prefix_closed u v h

instance : PartialOrder (BFTreeN n) where
  le t u := t.K ⊆ u.K
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := BFTreeN.ext (Set.Subset.antisymm h₁ h₂)

/-- Bottom has no constructor positions. -/
@[simp] theorem mem_bot (w : List (Fin n)) : w ∉ bot.K := by simp [bot]
/-- The root of a constructor tree is present. -/
@[simp] theorem nil_mem_node (a : Fin n → BFTreeN n) : [] ∈ (node a).K := trivial
/-- A nonempty constructor position belongs to the selected child. -/
@[simp] theorem cons_mem_node (a : Fin n → BFTreeN n) (i : Fin n)
    (w : List (Fin n)) : i :: w ∈ (node a).K ↔ w ∈ (a i).K := Iff.rfl

/-- Constructor trees are ordered componentwise. -/
@[simp] theorem node_le_node (a b : Fin n → BFTreeN n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w hw
    exact h (show i :: w ∈ (node a).K from hw)
  · intro h w hw
    cases w with
    | nil => trivial
    | cons i w => exact h i hw

/-- Bottom lies below every tree. -/
@[simp] theorem bot_le (t : BFTreeN n) : bot ≤ t := Set.empty_subset _

/-- A constructor root cannot lie below bottom. -/
theorem not_node_le_bot (a : Fin n → BFTreeN n) : ¬ node a ≤ bot := by
  intro h
  exact mem_bot [] (h (nil_mem_node a))

/-- Residual at a word, including absent positions (whose residual is empty). -/
def residual (t : BFTreeN n) (w : List (Fin n)) : BFTreeN n where
  K := {v | w ++ v ∈ t.K}
  prefix_closed := by
    intro u v h
    exact t.prefix_closed (w ++ u) v (by simpa [List.append_assoc] using h)

/-- The child at the given constructor position. -/
def subtree (t : BFTreeN n) (i : Fin n) : BFTreeN n := t.residual [i]

/-- Every tree is bottom or a constructor applied to its children. -/
theorem bot_or_node (t : BFTreeN n) :
    t = bot ∨ t = node t.subtree := by
  classical
  by_cases h : [] ∈ t.K
  · right
    ext w
    cases w with
    | nil => simp [h]
    | cons i w => rfl
  · left
    ext w
    simp only [mem_bot, iff_false]
    intro hw
    exact h (t.prefix_closed [] w hw)

end BFTreeN

/-- Flat covariant inequalities and equations to bottom. -/
inductive Lit (n : ℕ) (V : Type*) where
  /-- A variable inequality `u ≤ v`. -/
  | le (u v : V)
  /-- A constructor lower bound `f(a) ≤ u`. -/
  | fle (a : Fin n → V) (u : V)
  /-- A constructor upper bound `u ≤ f(a)`. -/
  | lef (u : V) (a : Fin n → V)
  /-- An equation `u = ⊥`. -/
  | bot (u : V)
  deriving DecidableEq

/-- Constructor-lower-bound arguments, for list-based computable filters. -/
def Lit.fleArgs? {V : Type*} : Lit n V → Option ((Fin n → V) × V)
  | .fle a u => some (a, u)
  | _ => none

/-- Constructor-upper-bound arguments, for list-based computable filters. -/
def Lit.lefArgs? {V : Type*} : Lit n V → Option (V × (Fin n → V))
  | .lef u a => some (u, a)
  | _ => none

/-- The lower-constructor accessor recognizes exactly lower-constructor literals. -/
@[simp] theorem Lit.mem_fleArgs? {V : Type*} (l : Lit n V) (a : Fin n → V) (u : V) :
    (a, u) ∈ l.fleArgs? ↔ l = .fle a u := by cases l <;> simp [Lit.fleArgs?]

/-- The upper-constructor accessor recognizes exactly upper-constructor literals. -/
@[simp] theorem Lit.mem_lefArgs? {V : Type*} (l : Lit n V) (u : V) (a : Fin n → V) :
    (u, a) ∈ l.lefArgs? ↔ l = .lef u a := by cases l <;> simp [Lit.lefArgs?]

/-- Interpret a literal under a tree assignment. -/
def Lit.Holds {V : Type*} (ρ : V → BFTreeN n) : Lit n V → Prop
  | .le u v => ρ u ≤ ρ v
  | .fle a u => BFTreeN.node (ρ ∘ a) ≤ ρ u
  | .lef u a => ρ u ≤ BFTreeN.node (ρ ∘ a)
  | .bot u => ρ u = BFTreeN.bot

/-- Rename the variables of a literal. -/
def Lit.map {V W : Type*} (f : V → W) : Lit n V → Lit n W
  | .le u v => .le (f u) (f v)
  | .fle a u => .fle (f ∘ a) (f u)
  | .lef u a => .lef (f u) (f ∘ a)
  | .bot u => .bot (f u)

/-- Renaming a literal agrees with precomposing its assignment. -/
@[simp] theorem Lit.holds_map {V W : Type*} (f : V → W) (ρ : W → BFTreeN n)
    (l : Lit n V) : (l.map f).Holds ρ ↔ l.Holds (ρ ∘ f) := by cases l <;> rfl

/-- Every literal in the constraint list holds. -/
def Sat {V : Type*} (ρ : V → BFTreeN n) (χ : List (Lit n V)) : Prop :=
  ∀ l ∈ χ, l.Holds ρ

/-- A tree has finitely many constructor positions. -/
def IsFiniteTree (t : BFTreeN n) : Prop := t.K.Finite

/-- A tree has finitely many distinct residual languages. -/
def IsRegularTree (t : BFTreeN n) : Prop :=
  (Set.range fun w => (t.residual w).K).Finite

/-- Every solution in the chosen tree class extends within that class. -/
def ExistsEntailsIn {X Z : Type*} (C : BFTreeN n → Prop)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  ∀ ρ, (∀ x, C (ρ x)) → Sat ρ φ →
    ∃ σ, (∀ z, C (σ z)) ∧ Sat (Sum.elim ρ σ) ψ

/-- Existential entailment over arbitrary bottom-only trees. -/
def ExistsEntails {X Z : Type*} (φ : List (Lit n X))
    (ψ : List (Lit n (X ⊕ Z))) : Prop := ExistsEntailsIn (fun _ => True) φ ψ

/-- A visible inequality with no hidden occurrences gives ordinary entailment. -/
theorem existsEntails_le_iff {X Z : Type*} (φ : List (Lit n X)) (x y : X) :
    ExistsEntails φ [(Lit.le (Sum.inl x) (Sum.inl y) : Lit n (X ⊕ Z))] ↔
      ∀ ρ, Sat ρ φ → ρ x ≤ ρ y := by
  constructor
  · intro h ρ hρ
    obtain ⟨σ, _, hσ⟩ := h ρ (fun _ => True.intro) hρ
    exact hσ (.le (.inl x) (.inl y)) (by simp)
  · intro h ρ _ hρ
    refine ⟨fun _ => BFTreeN.bot, fun _ => True.intro, ?_⟩
    simpa [Sat, Lit.Holds] using h ρ hρ


end DeciENSSE.Core
