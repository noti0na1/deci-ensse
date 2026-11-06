import DeciENSSE.Anchored.Estimate

/-! # Monotonicity of the anchored constants

The constants of the anchored bound (`eq:mo-constants`) are nondecreasing in each argument:
the type bound `C♯(N, d)`, the allowance `A♯(N, d)`, the dictionary bound `G♯(N, d)`, the
exponent `Ξ♯(N, d)`, the length bound `L♯(N, d)`, and, for monitors with at least one state,
the column bounds `col(M, k)` and `pcol(M, k)`. The mortal estimate (`lem:mo-estimate`)
replaces the state count and the depth by powers of two through this monotonicity.

## Main declarations

- `colBound_mono`, `pcolBound_mono`: the column bounds in the number of states and tracks.
- `anchoredTypeBound_mono`, `anchoredAllowance_mono`, `anchoredDictionaryBound_mono`,
  `anchoredExponent_mono`: the constants in the number of cores and the depth.
- `anchoredLengthBound_mono`: `L♯(N, d) ≤ L♯(N', d')` for `N ≤ N'` and `d ≤ d'`.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.BoundedDepth DeciNSSE.NormalForm

/-- `a ^ m ≤ b ^ n` for `1 ≤ a ≤ b` and `m ≤ n`. -/
private theorem pow_le_pow_of_le {a b m n : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hmn : m ≤ n) :
    a ^ m ≤ b ^ n :=
  (Nat.pow_le_pow_left hab m).trans (Nat.pow_le_pow_right (by omega) hmn)

/-- `N ^ N` is nondecreasing in `N`. -/
private theorem self_pow_le_self_pow {N N' : ℕ} (h : N ≤ N') : N ^ N ≤ N' ^ N' := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos N' with rfl | hN'
    · rfl
    · simpa using Nat.one_le_pow N' N' hN'
  · exact pow_le_pow_of_le hN h h

/-- The column bound of a monitor with at least one state is positive. -/
theorem colBound_pos {M : ℕ} (hM : 1 ≤ M) (k : ℕ) : 0 < colBound M k := by
  obtain ⟨M, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  unfold colBound
  positivity

/-- The column bound is nondecreasing in the number of states and of tracks, for monitors
with at least one state. -/
theorem colBound_mono {M M' k k' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M') (hk : k ≤ k') :
    colBound M k ≤ colBound M' k' := by
  refine le_trans ?_ (colBound_mono_core hMM (hM.trans hMM))
  have h1 : 1 ≤ M ^ (M + 1) := Nat.one_le_pow _ _ hM
  have h2 : 1 ≤ (2 ^ M) ^ (M + 1) := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  have h3 : 1 ≤ (2 ^ (M + 1)) ^ (M + 1) := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  unfold colBound
  apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul _ _) _) _
  · exact Nat.pow_le_pow_right h1 hk
  · exact Nat.pow_le_pow_right h2 hk
  · exact pow_le_pow_of_le Nat.one_le_two_pow (Nat.pow_le_pow_right (by decide) hk) hk
  · exact pow_le_pow_of_le (Nat.one_le_pow _ _ h3) (Nat.pow_le_pow_right h3 hk) hk

/-- The positive column bound of a monitor with at least one state is positive. -/
theorem pcolBound_pos {M : ℕ} (hM : 1 ≤ M) (k : ℕ) : 0 < pcolBound M k := by
  have h := colBound_pos hM k
  unfold pcolBound
  positivity

/-- The positive column bound is nondecreasing in the number of states and of tracks, for
monitors with at least one state. -/
theorem pcolBound_mono {M M' k k' : ℕ} (hM : 1 ≤ M) (hMM : M ≤ M') (hk : k ≤ k') :
    pcolBound M k ≤ pcolBound M' k' := by
  have hc := colBound_mono hM hMM hk
  have hs : ((2 ^ M) ^ (M + 1)) ^ k ≤ ((2 ^ M') ^ (M' + 1)) ^ k' :=
    pow_le_pow_of_le (Nat.one_le_pow _ _ Nat.one_le_two_pow)
      (pow_le_pow_of_le Nat.one_le_two_pow (Nat.pow_le_pow_right (by decide) hMM) (by omega)) hk
  unfold pcolBound
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc hc) hs) hs)
    (Nat.pow_le_pow_right (by decide) hk)

/-- The anchored type bound `C♯(N, d)` is nondecreasing. -/
theorem anchoredTypeBound_mono {N N' d d' : ℕ} (hN : N ≤ N') (hd : d ≤ d') :
    anchoredTypeBound N d ≤ anchoredTypeBound N' d' := by
  unfold anchoredTypeBound normalTypeBound DeciNSSE.Exchange.typeBound
  apply Nat.mul_le_mul (Nat.mul_le_mul (self_pow_le_self_pow hN) _) <;>
    exact Nat.pow_le_pow_right (by decide) (by gcongr)

/-- The anchored allowance `A♯(N, d)` is nondecreasing. -/
theorem anchoredAllowance_mono {N N' d d' : ℕ} (hN : N ≤ N') (hd : d ≤ d') :
    anchoredAllowance N d ≤ anchoredAllowance N' d' := by
  have := anchoredTypeBound_mono hN hd
  unfold anchoredAllowance
  omega

/-- The anchored dictionary bound `G♯(N, d)` is nondecreasing. -/
theorem anchoredDictionaryBound_mono {N N' d d' : ℕ} (hN : N ≤ N') (hd : d ≤ d') :
    anchoredDictionaryBound N d ≤ anchoredDictionaryBound N' d' := by
  unfold anchoredDictionaryBound
  exact Nat.add_le_add_left (Nat.mul_le_mul (anchoredAllowance_mono hN hd)
    (Nat.pow_le_pow_right (by decide) hd)) 2

/-- The exponent `Ξ♯(N, d)` of the closed form is nondecreasing. -/
theorem anchoredExponent_mono {N N' d d' : ℕ} (hN : N ≤ N') (hd : d ≤ d') :
    anchoredExponent N d ≤ anchoredExponent N' d' := by
  unfold anchoredExponent
  gcongr

/-- The anchored length bound `L♯(N, d)` is nondecreasing. -/
theorem anchoredLengthBound_mono {N N' d d' : ℕ} (hN : N ≤ N') (hd : d ≤ d') :
    anchoredLengthBound N d ≤ anchoredLengthBound N' d' := by
  unfold anchoredLengthBound posDescentFactor
  apply Nat.mul_le_mul (by omega)
  exact pow_le_pow_of_le (pcolBound_pos (by omega) _)
    (pcolBound_mono (by omega) (by omega) (anchoredDictionaryBound_mono hN hd)) hd

end DeciENSSE.Anchored
