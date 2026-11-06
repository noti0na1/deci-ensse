import DeciENSSE.Bounds

/-! # Paper contract: the size of the mortal bound

Contract entries for the estimate of the mortal bound (`lem:mo-estimate`) and its value at
the extracted instances (`cor:mo-extracted`), from the section *Mortal Holes*
(`sec:mo-short`).

Only library results and logical packaging are used below. The mortal bound `Len♯_I` of an
instance with state types `SA, SB, SA', SB'` (the paper's `A, B, A', B'`) is
`Core.Words.Mortal.mortalHoleBound` at their cardinalities, and its Π-reader has the states
`Core.Words.Mortal.State`, all of them counted. For the extracted instances, this bound is
`Core.Mixed.extractedBoundSelf`.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Core.Mixed Core.Words Bounds

variable {n : ℕ}

/-- **Lemma (Mortal bound)**, `lem:mo-estimate`.
Form: N-bar is the cardinality of the reader-state type Mortal.State, and Len-sharp is mortalHoleBound at the four cardinalities; this numerical estimate requires no automaton instance and also permits empty state carriers.
-/
theorem lem_mo_estimate {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA']
    [Fintype SB'] {α β : ℕ} (hα : 3 ≤ α)
    (hN : Fintype.card (Mortal.State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) ≤ 2 ^ α)
    (hA : Fintype.card SA ≤ 2 ^ β) :
    Mortal.mortalHoleBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA')
      (Fintype.card SB') ≤ E3 (3 * α + 2 * β + 9) :=
  mortalHoleBound_le_E3 hα
    ((Mortal.card_state (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) ▸ hN) hA

/-- **Corollary (Mortal bound for extracted instances)**, `cor:mo-extracted`.
Form: Len-sharp of I_pq is extractedBoundSelf mortalHoleBound X Z, the mortal bound at the state counts of extractSelf, the same for all p and q; the separator word u#t has length |u| + |t| + 1.
-/
theorem cor_mo_extracted {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (hs : 1 ≤ Fintype.card X + Fintype.card Z) :
    (extractedBoundSelf Mortal.mortalHoleBound X Z ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (22 * (Fintype.card X + Fintype.card Z) + 15)) ∧
    ∀ p q : X × Bool, (extractSelf c φ ψ p q).HasMortalHole →
      ∃ u t, (extractSelf c φ ψ p q).IsMortalHole u t ∧
        u.length + t.length + 1 ≤ E3 (22 * (Fintype.card X + Fintype.card Z) + 15) :=
  ⟨extracted_mortalHoleBound_le hs, exists_short_extracted_mortalHole c φ ψ⟩

end DeciENSSE.Paper
