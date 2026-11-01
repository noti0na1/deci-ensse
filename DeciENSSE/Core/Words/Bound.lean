import DeciENSSE.Core.Words.Pump
import DeciENSSE.Core.Words.Mortal.Bound

/-! # Short-hole bounds over finite alphabets

The maximum of the non-mortal pumping bound and elementary mortal compression
bound applies to every finite alphabet, including the empty alphabet.

## Main declarations

- `existsHoleBound`
- `nonMortalShortHoleBound`
- `shortHoleBound`
-/

set_option autoImplicit false

namespace DeciENSSE.Core

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The maximum of the non-mortal and elementary mortal bounds. -/
def existsHoleBound (a b c d : ℕ) : ℕ :=
  max (nonMortalHoleBound a b c d) (mortalHoleBound a b c d)

/-- Assemble a hole bound from a purely periodic pre-hole bound. -/
theorem shortHoleBound_of_periodic [Inhabited α]
    (hperiodic : ∀ a b c d, ∀ I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d),
      I.PurelyPeriodicShortPreHole (nonMortalPreHoleCapacity a b c d)) :
    ShortHoleBound α existsHoleBound :=
  shortHoleBound_of_split threeCases
    (nonMortalShortHoleBound_of_periodic hperiodic) mortalShortHoleBound

/-- The pump supplies the periodic premise of the non-mortal bound. -/
theorem nonMortalShortHoleBound [Inhabited α] :
    NonMortalShortHoleBound α nonMortalHoleBound :=
  nonMortalShortHoleBound_pump

/-- Every FH instance over any finite alphabet has a bounded hole if it has one. -/
theorem shortHoleBound (α : Type*) [Fintype α] [DecidableEq α] :
    ShortHoleBound α existsHoleBound := by
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
    exact shortHoleBound_of_split threeCases nonMortalShortHoleBound mortalShortHoleBound

namespace BoundExamples

/-- The assembled bound includes the empty alphabet. -/
theorem empty_alphabet : ShortHoleBound (Fin 0) existsHoleBound := shortHoleBound _

/-- The assembled bound includes a one-letter alphabet. -/
theorem unary_alphabet : ShortHoleBound (Fin 1) existsHoleBound := shortHoleBound _

/-- The assembled bound includes a two-letter alphabet. -/
theorem binary_alphabet : ShortHoleBound Bool existsHoleBound := shortHoleBound _

/-- Apply the full bound to a genuine ternary FH instance with a hole. -/
theorem ternary_bounded :
    ∃ u t, CoreExamples.ternaryBranch.IsHole u t ∧
      u.length + t.length ≤ existsHoleBound 2 1 1 2 :=
  shortHoleBound (Fin 3) 2 1 1 2 _
    CoreExamples.short_hypotheses.1 CoreExamples.short_hypotheses.2

/-- The empty-alphabet branch has actual FH/hole inputs. -/
theorem empty_hypotheses :
    let I := CoreExamples.smallInstance (CoreExamples.oneDFA (α := Fin 0)) ∅
    I.FH ∧ I.IsHole [] [] :=
  ⟨CoreExamples.smallInstance_fh _ _, by decide +kernel⟩

end BoundExamples


end DeciENSSE.Core
