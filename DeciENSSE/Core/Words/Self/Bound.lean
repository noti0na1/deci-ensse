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

/-- Explicit computable maximum of the non-mortal and mortal bounds. -/
def selfHoleBound (a b c d : ℕ) : ℕ :=
  max (pumpHoleBound a b c d) (mortalHoleBound a b c d)

/-- Self-aware pumping supplies the periodic shortening premise. -/
theorem nonMortalShortHoleBoundSelf [Inhabited α] : NonMortalShortHoleBoundSelf α pumpHoleBound :=
  nonMortalShortHoleBoundSelf_of_periodic purelyPeriodicShortPreHole_capacity

/-- Every ForcedHeads instance with a self-aware hole has one within the explicit bound. -/
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
