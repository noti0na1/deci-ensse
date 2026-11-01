import DeciENSSE.Core.Words.Self.Bound

/-! # Short-hole bounds over finite alphabets

A two-word instance is a self-guarded instance with an empty self guard. Specializing
the self-guarded bound gives a short hole over every finite alphabet, including the
empty alphabet.

## Main declarations

- `twoWordHoleBound`: the self-guarded bound specialized to plain instances.
- `shortHoleBound`: every instance with forced target heads and a hole has a short hole.
-/

namespace DeciENSSE.Core.Words

/-- The maximum of the polynomial pumping bound and elementary mortal bound. -/
def twoWordHoleBound (a b c d : ℕ) : ℕ := Self.selfHoleBound a b c d

/-- Every instance with forced target heads and a hole has a bounded hole. -/
theorem shortHoleBound (α : Type*) [Fintype α] [DecidableEq α] :
    ShortHoleBound α twoWordHoleBound := by
  intro a b c d I hf hh
  obtain ⟨u, t, ht⟩ := hh
  obtain ⟨v, w, hvw, hlen⟩ := Self.shortHoleBoundSelf α a b c d I.toSelf hf
    ⟨u, t, (I.isHole_toSelf_iff u t).mpr ht⟩
  exact ⟨v, w, (I.isHole_toSelf_iff v w).mp hvw, hlen⟩

end DeciENSSE.Core.Words
