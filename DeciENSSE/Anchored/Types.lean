import DeciENSSE.Anchored.NormalForm

/-! # The number of anchored exchange types

The anchored exchange type of a letter at level `i` takes values in a finite type space:
the closed exchange type of the level monitor together with the positive rows of the
derived channel, relative to the ordinary cores, the used cores and the protected letters.
At a level below the depth of a nonempty word of depth at most `d`, this space has at most
`anchoredTypeBound N d = N ^ N · 2 ^ (5 N² + 10 N (N + d) (d + 1) + 7 N + 1)` elements, for
`N` base cores. The count is the one used inside `posNormalAt_alphCard_le`.

## Main declarations

- `anchoredTypeBound_eq`: the closed form of `anchoredTypeBound`.
- `card_anchoredType_le`: the number of anchored exchange types at a level.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.Exchange DeciNSSE.NormalForm
  DeciNSSE.HierarchyDepth DeciNSSE.StartCores

/-- The closed form of the number of anchored exchange types. -/
theorem anchoredTypeBound_eq (N d : ℕ) :
    anchoredTypeBound N d =
      N ^ N * 2 ^ (5 * N ^ 2 + 10 * N * (N + d) * (d + 1) + 7 * N + 1) := by
  unfold anchoredTypeBound normalTypeBound typeBound
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]

/-- At a level `i` below the depth `D ≤ d` of a nonempty word, the anchored exchange types
relative to the protected letters take at most `anchoredTypeBound N d` values: the type
space, the codomain of `anchoredType`, has at most that many elements. -/
theorem card_anchoredType_le (D0 : Lettered α Q) {w : List α} {i d : ℕ} (hw : w ≠ [])
    (hid : i < depth w) (hd : depth w ≤ d) :
    Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) (Pset D0 w i) ×
      PosRows (Qset Q i) (Uset D0 w i) (Pset D0 w i)) ≤
      anchoredTypeBound (Fintype.card Q) d := by
  have hs : sCount D0 w i ≤ d := (sCount_le_level D0 hw i).trans (by omega)
  have hp : (Pset D0 w i).card ≤ d + 1 := (card_Pset_le D0 w i).trans (by omega)
  have hU := card_Uset_le D0 w i
  rw [Fintype.card_prod, card_posRows, card_Qset]
  unfold anchoredTypeBound
  apply Nat.mul_le_mul
  · refine (card_exType_le D0 w i (Pset D0 w i)).trans ?_
    unfold normalTypeBound typeBound
    gcongr
  · apply Nat.pow_le_pow_right (by decide)
    have h1 : (Uset D0 w i).card ≤ Fintype.card Q + d := by omega
    have h2 : 6 * Fintype.card Q * (Uset D0 w i).card * (Pset D0 w i).card ≤
        6 * Fintype.card Q * (Fintype.card Q + d) * (d + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) hp
    omega

end DeciENSSE.Anchored
