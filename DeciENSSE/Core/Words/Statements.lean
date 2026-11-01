import DeciENSSE.Core.Words.TwoWordInstance

/-! # Short-hole bound statements

A hole bound depends on the four automaton state counts. `ShortHoleBound` states that
every instance with forced target heads and a hole has a hole within that bound.
The state types are `Fin n`; a start state rules out an empty state type.

## Main declarations

- `HoleBound`: a function of four state counts.
- `ShortHoleBound`: the bounded-hole property.
-/

namespace DeciENSSE.Core.Words

/-- A length bound in terms of the state counts of `A`, `B`, `A'` and `B'`. -/
abbrev HoleBound := ℕ → ℕ → ℕ → ℕ → ℕ

/-- Every instance with forced target heads and a hole has a hole `(u, t)` with
`|u| + |t| ≤ B`. -/
def ShortHoleBound (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : TwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
    I.ForcedHeads → I.HasHole → ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ B a b c d

end DeciENSSE.Core.Words
