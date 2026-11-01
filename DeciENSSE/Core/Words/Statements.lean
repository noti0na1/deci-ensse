import DeciENSSE.Core.Words.SS2

/-! # Short-hole bounds and the three cases

A hole bound is a function of the four state counts of an instance. This module states
that every instance with forced target heads and a hole has a hole within the bound, and
the same for the non-mortal cases and for mortal holes. If every hole falls into a
non-mortal case or is witnessed by a mortal hole (the three cases), the two partial bounds
combine into one.

These are definitions; none of them is asserted here. State types are `Fin n`, which
keeps the statements in one universe; the start states exclude empty state types.
"Non-mortal" refers to the two cases of `SS2.NonMortalCase`, not to the negation of
mortality of the final spine state of a particular hole.

## Main declarations

- `HoleBound`: bounds in terms of the four state counts.
- `ShortHoleBound`, `NonMortalShortHoleBound`, `MortalShortHoleBound`: short holes for all
  instances, in the non-mortal cases, and for mortal holes.
- `ThreeCases`: every hole falls into a non-mortal case or there is a mortal hole.
- `shortHoleBound_of_split`: the two partial bounds give a bound for all holes.

The declarations are in the namespace `DeciENSSE.Core`.
-/

namespace DeciENSSE.Core

/-- A length bound in terms of the state counts of `A`, `B`, `A'` and `B'`. -/
abbrev HoleBound := ℕ → ℕ → ℕ → ℕ → ℕ

/-- Every instance with forced target heads and a hole has a hole `(u, t)` with
`|u| + |t| ≤ B`. -/
def ShortHoleBound (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.HasHole → ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ B a b c d

/-- Every instance with forced target heads in a non-mortal case has a hole `(u, t)` with
`|u| + |t| ≤ B`. -/
def NonMortalShortHoleBound (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) :
    Prop :=
  ∀ a b c d, ∀ I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.NonMortalCase →
      ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ B a b c d

/-- Every instance with forced target heads and a mortal hole has a mortal hole `(u, t)`
with `|u| + |t| ≤ B`. -/
def MortalShortHoleBound (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.HasMortalHole →
      ∃ u t, I.IsMortalHole u t ∧ u.length + t.length ≤ B a b c d

/-- The three cases: an instance with forced target heads has a hole iff it is in a
non-mortal case or has a mortal hole. -/
def ThreeCases (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  ∀ a b c d, ∀ I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → (I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The three cases combine a non-mortal and a mortal bound into a bound for all holes. -/
theorem shortHoleBound_of_split {B₁ B₂ : HoleBound} (hc : ThreeCases α)
    (hn : NonMortalShortHoleBound α B₁) (hm : MortalShortHoleBound α B₂) :
    ShortHoleBound α (fun a b c d => max (B₁ a b c d) (B₂ a b c d)) := by
  intro a b c d I hfh hh
  rcases (hc a b c d I hfh).mp hh with h | h
  · obtain ⟨u, t, hu, hb⟩ := hn a b c d I hfh h
    exact ⟨u, t, hu, hb.trans (le_max_left _ _)⟩
  · obtain ⟨u, t, hu, hb⟩ := hm a b c d I hfh h
    exact ⟨u, t, hu.1, hb.trans (le_max_right _ _)⟩

end DeciENSSE.Core
