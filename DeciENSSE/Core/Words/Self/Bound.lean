import DeciENSSE.Core.Words.Self.NonMortal
import DeciENSSE.Core.Words.Self.Pump
import DeciENSSE.Core.Words.Self.Mortal

/-! # Short-hole bounds with target self events

Non-mortal pumping and elementary mortal compression give a
bound for every finite alphabet, including the empty alphabet.

## Main declarations

- `selfHoleBound`
- `nonMortalShortHoleBoundSelf`
- `shortHoleBoundSelf`
-/

namespace DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Words.Mortal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The bound for all holes with self events: the maximum of the non-mortal bound `Lnm` and
the mortal bound. -/
def selfHoleBound (a b c d : ℕ) : ℕ :=
  max (pumpHoleBound a b c d) (mortalHoleBound a b c d)

/-- The bound `Lnm` in the non-mortal cases (`thm:nm-three-cases`, last claim),
for every finite alphabet: the pump with self events supplies the periodic shortening
premise, and over the empty alphabet neither non-mortal case can occur. -/
theorem nonMortalShortHoleBoundSelf : NonMortalShortHoleBoundSelf α pumpHoleBound := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    rintro a b c d I ⟨u, t, -, ⟨-, r, -, -, x, -⟩ | ⟨-, ξ, -⟩⟩
    · exact isEmptyElim x
    · exact isEmptyElim (ξ 0)
  | inr h =>
    have := Classical.inhabited_of_nonempty h
    exact nonMortalShortHoleBoundSelf_of_periodic purelyPeriodicShortPreHole_capacity

/-- **Short holes** (`thm:mo-decide`): over every finite alphabet, an instance with state counts
`a, b, c, d`, forced target heads and a hole has a hole `(u, t)` with
`|u| + |t| ≤ selfHoleBound a b c d`. -/
theorem shortHoleBoundSelf (α : Type*) [Fintype α] [DecidableEq α] :
    ShortHoleBoundSelf α selfHoleBound := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    have := h
    have empty (w : Word α) : w = [] := by
      cases w with
      | nil => rfl
      | cons x _ => exact isEmptyElim x
    intro a b c d I _ hh
    obtain ⟨u, t, ht⟩ := hh
    refine ⟨u, t, ht, ?_⟩
    simp only [empty u, empty t, List.length_nil, Nat.zero_add]
    exact Nat.zero_le _
  | inr h =>
    have := Classical.inhabited_of_nonempty h
    exact shortHoleBoundSelf_of_split three_cases_self nonMortalShortHoleBoundSelf
      mortalShortHoleBoundSelf

end DeciENSSE.Core.Words.Self
