import DeciENSSE.Core.Words.Mortal.Depth
import DeciENSSE.Core.Words.Statements
import DeciENSSE.Anchored.ElementaryBound

/-! # Short mortal holes

The Π-holes of the Π-reader are the positive holes of its lettered monitor with the base
channel of `Pi` and the separator, and they are the separator words of mortal holes. A
mortal hole has depth at most `d = 2 N |SA| - 1`, where `N = |RState|`, so elementary
anchored compression gives a Π-hole, hence a mortal hole, whose separator word has length at
most `anchoredLengthBound N d`. Forced target heads are not needed, and the bound does not
depend on the alphabet.

## Main declarations

- `mortalHoleBound`: the bound in terms of the four state counts.
- `Mortal.posHole_pi_iff`: positive holes of the base channel are the separator words of
  mortal holes.
- `Mortal.exists_short_mortalHole`: a mortal hole has a short mortal hole.
- `mortalShortHoleBound`: the short-mortal-hole statement with `mortalHoleBound`.

The declarations are in the namespace `DeciENSSE.Core`.
-/

namespace DeciENSSE.Core
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.HierarchyDepth
  DeciNSSE.Holes DeciNSSE.RejectedTail DeciENSSE.Anchored

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The mortal bound for state counts `a`, `b`, `c`, `d` of `A`, `B`, `A'`, `B'`: the
elementary anchored bound for the Π-reader, which has `N = 1 + ac + bd + ad` states, at the
depth `2 N a - 1`. -/
def mortalHoleBound (a b c d : ℕ) : ℕ :=
  let N := 1 + a * c + b * d + a * d
  anchoredLengthBound N (2 * N * a - 1)

namespace Mortal
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-- On a word with one separator, `HasPi` is the positive condition of the base channel. -/
theorem hasPi_iff_pos_of_count (w : List (Option α)) (hc : w.count none = 1) :
    HasPi I w ↔ Pos (ofReader (reader I) (Adm I) (Rej I))
      (baseChan (reader I) (Pi I) none) w := by
  obtain ⟨u, t, rfl⟩ := exists_sepWord w hc
  have hb := pos_base_iff_anchored (reader I) (Adm I) (Pi I) (Rej I) none
    (sepWord u t) u.length
    (by simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using hc)
    ((separator_unique u t _).mpr rfl)
  constructor
  · rintro ⟨p, _, hp, s, e, ha, hpi⟩
    have he := (separator_unique u t p).mp hp
    subst p
    apply hb.mpr
    exact ⟨s, ha.1, ha.2.1 ▸ ha.2.2, ha.2.1 ▸ hpi⟩
  · intro hp
    obtain ⟨s, hs, he, hpi⟩ := hb.mp hp
    exact ⟨u.length, hc, (separator_unique u t _).mpr rfl,
      s, _, ⟨hs, rfl, he⟩, hpi⟩

/-- A hole of the lettered monitor of the Π-reader has exactly one separator. -/
theorem hole_count_separator {w : List (Option α)}
    (hw : (ofReader (reader I) (Adm I) (Rej I)).IsHole w) :
    w.count none = 1 := by
  have hh := (isHole_ofReader_iff _ _ _ hw.ne_nil).mp hw
  exact rejected_count_separator I w ((isReaderHole_iff _ _ _ _).mp hh).1

/-- On holes, `HasPi` is the positive condition of the base channel. -/
theorem hasPi_iff_pos_of_hole {w : List (Option α)}
    (hw : (ofReader (reader I) (Adm I) (Rej I)).IsHole w) :
    HasPi I w ↔ Pos (ofReader (reader I) (Adm I) (Rej I))
      (baseChan (reader I) (Pi I) none) w :=
  hasPi_iff_pos_of_count I w (hole_count_separator I hw)

/-- The positive holes of the base channel are exactly the separator words of mortal holes,
for every word. -/
theorem posHole_pi_iff (w : List (Option α)) :
    PosHole (ofReader (reader I) (Adm I) (Rej I))
      (baseChan (reader I) (Pi I) none) w ↔
      ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  rw [← ofReader_pi_iff I w]
  exact and_congr_right (fun hw => (hasPi_iff_pos_of_hole I hw).symm)

/-- A mortal hole has a mortal hole whose separator word has length at most the mortal
bound; forced target heads are not needed. -/
theorem exists_short_mortalHole {u t : Word α} (h : I.IsMortalHole u t) :
    ∃ u' t', I.IsMortalHole u' t' ∧
      u'.length + t'.length + 1 ≤
        mortalHoleBound (Fintype.card SA) (Fintype.card SB)
          (Fintype.card SA') (Fintype.card SB') := by
  obtain ⟨hh, hpi, hd⟩ := mortal_compression_input I h
  have hp : PosHole (ofReader (reader I) (Adm I) (Rej I))
      (baseChan (reader I) (Pi I) none) (sepWord u t) :=
    ⟨hh, (hasPi_iff_pos_of_hole I hh).mp hpi⟩
  obtain ⟨w', hw', -, hlen⟩ := exists_short_posHole_elementary hp
    ⟨depth (sepWord u t), hd, isUnary_depth _⟩
  obtain ⟨u', t', rfl, hm⟩ := (posHole_pi_iff I w').mp hw'
  refine ⟨u', t', hm, ?_⟩
  simpa only [mortalHoleBound, card_state, length_sepWord, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hlen

/-- `small` has a short mortal hole. -/
theorem Examples.mortal_compressed :
    ∃ u t, Examples.small.IsMortalHole u t ∧
      u.length + t.length + 1 ≤ mortalHoleBound 4 2 2 2 := by
  simpa only [Fintype.card_fin] using
    exists_short_mortalHole Examples.small Examples.mortal_01_1

end Mortal

/-- Every instance with forced target heads and a mortal hole has a mortal hole within
`mortalHoleBound`. -/
theorem mortalShortHoleBound : MortalShortHoleBound α mortalHoleBound := by
  intro a b c d I _ h
  obtain ⟨u, t, hm⟩ := h
  obtain ⟨u', t', hm', hlen⟩ := Mortal.exists_short_mortalHole I hm
  refine ⟨u', t', hm', ?_⟩
  simp only [Fintype.card_fin] at hlen
  omega

/-- The hypotheses of `mortalShortHoleBound` are satisfiable. -/
theorem Mortal.Examples.ternary_public_bound :
    ∃ u t, CoreExamples.ternaryMortal.IsMortalHole u t ∧
      u.length + t.length ≤ mortalHoleBound 2 1 1 2 :=
  mortalShortHoleBound 2 1 1 2 CoreExamples.ternaryMortal
    CoreExamples.mortal_hypotheses.1 CoreExamples.mortal_hypotheses.2

end DeciENSSE.Core
