import DeciENSSE.Core.Words.Self.NonMortalS
import DeciENSSE.Core.Words.Self.PumpS
import DeciENSSE.Core.Words.Self.MortalS

/-! # Short-hole bounds with target self events

Non-mortal pumping and elementary mortal compression give an unconditional
bound for every finite alphabet, including the empty alphabet.

## Main declarations

- `existsHoleBoundS`
- `nonMortalShortHoleBoundS`
- `shortHoleBoundS`
-/

set_option autoImplicit false

namespace DeciENSSE.Core

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Explicit computable maximum of the non-mortal and mortal bounds. -/
def existsHoleBoundS (a b c d : ℕ) : ℕ :=
  max (pumpHoleBound a b c d) (mortalHoleBound a b c d)

/-- Self-aware pumping supplies the periodic shortening premise. -/
theorem nonMortalShortHoleBoundS [Inhabited α] : NonMortalShortHoleBoundS α pumpHoleBound :=
  nonMortalShortHoleBoundS_of_periodic purelyPeriodicShortPreHoleS_capacity

/-- Every FH instance with a self-aware hole has one within the explicit bound. -/
theorem shortHoleBoundS (α : Type*) [Fintype α] [DecidableEq α] :
    ShortHoleBoundS α existsHoleBoundS := by
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
    exact shortHoleBoundS_of_split threeCasesS nonMortalShortHoleBoundS mortalShortHoleBoundS

namespace BoundSExamples

/-- The assembled bound includes the empty alphabet. -/
theorem empty_alphabet : ShortHoleBoundS (Fin 0) existsHoleBoundS := shortHoleBoundS _

/-- The assembled bound includes a one-letter alphabet. -/
theorem unary_alphabet : ShortHoleBoundS (Fin 1) existsHoleBoundS := shortHoleBoundS _

/-- The assembled bound includes a two-letter alphabet. -/
theorem binary_alphabet : ShortHoleBoundS Bool existsHoleBoundS := shortHoleBoundS _

/-- A genuine ternary hole with nonempty self guard exercises the assembled bound. -/
theorem ternary_bounded :
    ∃ u t, NonMortalSExamples.ternaryPending.IsHoleS u t ∧
      u.length + t.length ≤ existsHoleBoundS 2 2 2 2 :=
  shortHoleBoundS (Fin 3) 2 2 2 2 _ NonMortalSExamples.ternaryPending_fh
    ⟨[1, 2], [1, 2], NonMortalSExamples.ternary_pending_completion⟩

/-- Self guards may be nonempty even when the alphabet is empty. -/
def emptyInstance : SS2Self (Fin 0) (Fin 1) (Fin 1) (Fin 1) (Fin 2) where
  toSS2 := CoreExamples.smallInstance CoreExamples.oneDFA ∅
  SelfGuard := {(0, 0)}

/-- An empty-alphabet instance satisfies the finite-head and hole hypotheses. -/
theorem empty_hypotheses : emptyInstance.FH ∧ emptyInstance.IsHoleS [] [] :=
  ⟨CoreExamples.smallInstance_fh _ _, by decide +kernel⟩

end BoundSExamples


end DeciENSSE.Core
