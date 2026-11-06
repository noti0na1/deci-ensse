import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ext

/-! # Prefix-closed sets and covariant pushdown rules

Two pieces of syntax that the variance proof uses below the leaf cones.

* A `PrefixSet` is a set of words over `Fin n` closed under taking prefixes, ordered by
  inclusion. The observations of `Core.Full.AC` are prefix sets.
* A covariant system is a list of rules `Lit`: variable inequalities `u ≤ v` and constructor
  bounds `f(a) ≤ u` and `u ≤ f(a)`. A configuration `(v, w)` pairs a variable with a stack word,
  and a rule acts on configurations as a pushdown move (`Move`): an inequality copies, a lower
  bound pushes the child index, an upper bound pops it. `Mixed.signedSys` produces these systems
  from the signed translation of a full system, and the automata of `Core/Automata` summarize
  their move paths.

## Main declarations

- `PrefixSet`, `PrefixSet.node`, `PrefixSet.residual`: prefix-closed sets of words.
- `Lit`, `Lit.fleArgs?`, `Lit.lefArgs?`: covariant rules and their computable accessors.
- `Config`, `Move`: configurations and pushdown moves.
-/

namespace DeciENSSE.Core

variable {n : ℕ}

/-! ## Prefix-closed sets of words -/

/-- A set of words closed under taking prefixes. -/
@[ext] structure PrefixSet (n : ℕ) where
  /-- The words of the set. -/
  carrier : Set (List (Fin n))
  /-- Every prefix of a member is a member. -/
  prefix_closed : ∀ u v, u ++ v ∈ carrier → u ∈ carrier

namespace PrefixSet

/-- The empty prefix set. -/
def bot : PrefixSet n := ⟨∅, by simp⟩

/-- The prefix set containing the empty word and `i :: w` for every `w` in the `i`-th set. -/
def node (a : Fin n → PrefixSet n) : PrefixSet n where
  carrier w := match w with
    | [] => True
    | i :: v => v ∈ (a i).carrier
  prefix_closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons i u => exact (a i).prefix_closed u v h

/-- Prefix sets are ordered by inclusion. -/
instance : PartialOrder (PrefixSet n) where
  le t u := t.carrier ⊆ u.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := PrefixSet.ext (Set.Subset.antisymm h₁ h₂)

/-- The empty prefix set has no members. -/
@[simp] theorem mem_bot (w : List (Fin n)) : w ∉ (bot : PrefixSet n).carrier := by simp [bot]
/-- The empty word belongs to every `node`. -/
@[simp] theorem nil_mem_node (a : Fin n → PrefixSet n) : [] ∈ (node a).carrier := trivial
/-- A nonempty word of a `node` belongs to the selected set. -/
@[simp] theorem cons_mem_node (a : Fin n → PrefixSet n) (i : Fin n)
    (w : List (Fin n)) : i :: w ∈ (node a).carrier ↔ w ∈ (a i).carrier := Iff.rfl

/-- `node` is monotone and reflects the order componentwise. -/
@[simp] theorem node_le_node (a b : Fin n → PrefixSet n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w hw
    exact h (show i :: w ∈ (node a).carrier from hw)
  · intro h w hw
    cases w with
    | nil => trivial
    | cons i w => exact h i hw

/-- The empty prefix set is the least one. -/
@[simp] theorem bot_le (t : PrefixSet n) : bot ≤ t := Set.empty_subset _

/-- The residual at a word: the words `v` with `w ++ v` in the set. -/
def residual (t : PrefixSet n) (w : List (Fin n)) : PrefixSet n where
  carrier := {v | w ++ v ∈ t.carrier}
  prefix_closed := by
    intro u v h
    exact t.prefix_closed (w ++ u) v (by simpa [List.append_assoc] using h)

/-- The residual at a one-letter word. -/
def subtree (t : PrefixSet n) (i : Fin n) : PrefixSet n := t.residual [i]

end PrefixSet

/-! ## Covariant pushdown rules -/

/-- The rules of a covariant system. -/
inductive Lit (n : ℕ) (V : Type*) where
  /-- A variable inequality `u ≤ v`. -/
  | le (u v : V)
  /-- A constructor lower bound `f(a) ≤ u`. -/
  | fle (a : Fin n → V) (u : V)
  /-- A constructor upper bound `u ≤ f(a)`. -/
  | lef (u : V) (a : Fin n → V)
  deriving DecidableEq

/-- Constructor-lower-bound arguments, for list-based computable filters. -/
def Lit.fleArgs? {V : Type*} : Lit n V → Option ((Fin n → V) × V)
  | .fle a u => some (a, u)
  | _ => none

/-- Constructor-upper-bound arguments, for list-based computable filters. -/
def Lit.lefArgs? {V : Type*} : Lit n V → Option (V × (Fin n → V))
  | .lef u a => some (u, a)
  | _ => none

/-- The lower-constructor accessor recognizes exactly lower-constructor rules. -/
@[simp] theorem Lit.mem_fleArgs? {V : Type*} (l : Lit n V) (a : Fin n → V) (u : V) :
    (a, u) ∈ l.fleArgs? ↔ l = .fle a u := by cases l <;> simp [Lit.fleArgs?]

/-- The upper-constructor accessor recognizes exactly upper-constructor rules. -/
@[simp] theorem Lit.mem_lefArgs? {V : Type*} (l : Lit n V) (u : V) (a : Fin n → V) :
    (u, a) ∈ l.lefArgs? ↔ l = .lef u a := by cases l <;> simp [Lit.lefArgs?]

/-- A variable paired with a stack word. -/
abbrev Config (n : ℕ) (V : Type*) := V × List (Fin n)

/-- Pushdown moves on configurations: an inequality copies the stack, a lower bound
`f(a) ≤ u` pushes `i` from `a i` to `u`, and an upper bound `u ≤ f(a)` pops `i` from `u` to
`a i`. -/
inductive Move {V : Type*} (χ : List (Lit n V)) : Config n V → Config n V → Prop
  | copy {u v w} : Lit.le u v ∈ χ → Move χ (u, w) (v, w)
  | push {a u w} (i : Fin n) : Lit.fle a u ∈ χ →
      Move χ (a i, w) (u, i :: w)
  | pop {u a w} (i : Fin n) : Lit.lef u a ∈ χ →
      Move χ (u, i :: w) (a i, w)

end DeciENSSE.Core
