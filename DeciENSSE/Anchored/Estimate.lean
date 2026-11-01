import DeciENSSE.Anchored.ElementaryBound

/-! # A closed-form estimate of the anchored bound

The anchored dictionary allowance is at most `2 ^ Ξ` for the polynomial exponent
`Ξ(N, d) = 6 N² + 10 N (N + d) (d + 1) + 7 N + 3 d + 4`, and the anchored length allowance
is at most `2 ^ 2 ^ (5 Ξ + 6)`: two exponentials over a polynomial in the number of cores
and the depth.

## Main declarations

- `anchoredExponent`: the exponent `Ξ(N, d)`.
- `anchoredDictionaryBound_le`: `G♯(N, d) ≤ 2 ^ Ξ(N, d)`.
- `anchoredLengthBound_le`: `L♯(N, d) ≤ 2 ^ 2 ^ (5 Ξ(N, d) + 6)`.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.BoundedDepth DeciNSSE.NormalForm

/-- A power-of-two exponent for the anchored dictionary allowance. -/
def anchoredExponent (N d : ℕ) : ℕ :=
  6 * N ^ 2 + 10 * N * (N + d) * (d + 1) + 7 * N + 3 * d + 4

private theorem add_le_two_pow {a b p q : ℕ} (ha : a ≤ 2 ^ p) (hb : b ≤ 2 ^ q) :
    a + b ≤ 2 ^ (p + q + 1) := by
  have hp : 2 ^ p ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : 2 ^ q ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

/-- The anchored dictionary allowance is singly exponential in a polynomial in the number
of cores and the depth. -/
theorem anchoredDictionaryBound_le (N d : ℕ) :
    anchoredDictionaryBound N d ≤ 2 ^ anchoredExponent N d := by
  let E := 6 * N ^ 2 + 10 * N * (N + d) * (d + 1) + 7 * N + 1
  have hC : anchoredTypeBound N d ≤ 2 ^ E := by
    unfold anchoredTypeBound normalTypeBound DeciNSSE.Exchange.typeBound
    calc
      _ ≤ (2 ^ N) ^ N * 2 ^ (2 * N ^ 2 + 4 * N * (N + d) * (d + 1) + 3 * N) *
          2 ^ (3 * N ^ 2 + 6 * N * (N + d) * (d + 1) + 4 * N + 1) := by
        gcongr
        exact Nat.lt_two_pow_self.le
      _ = 2 ^ E := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        dsimp [E]
        ring
  have hA : anchoredAllowance N d ≤ 2 ^ (d + 1 + E + 1) :=
    add_le_two_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := d + 1))) hC
  have h3 : 3 ^ d ≤ 2 ^ (2 * d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide) d
  have hprod := Nat.mul_le_mul hA h3
  rw [← pow_add] at hprod
  have htwo : 2 ≤ 2 ^ (d + 1 + E + 1 + 2 * d) := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ d + 1 + E + 1 + 2 * d by omega)
    simpa using this
  unfold anchoredDictionaryBound
  calc
    _ ≤ 2 ^ (d + 1 + E + 1 + 2 * d) * 2 := by omega
    _ ≤ 2 ^ anchoredExponent N d := by
      rw [← pow_succ]
      apply Nat.pow_le_pow_right (by decide)
      dsimp [anchoredExponent, E]
      omega

/-- The anchored length allowance has two exponentials over a polynomial top exponent. -/
theorem anchoredLengthBound_le (N d : ℕ) :
    anchoredLengthBound N d ≤ 2 ^ 2 ^ (5 * anchoredExponent N d + 6) := by
  let H := anchoredExponent N d
  let M := N + d + 1
  let g := anchoredDictionaryBound N d
  have hH : M + 1 ≤ H := by dsimp [M, H, anchoredExponent]; omega
  have hM : M ≤ 2 ^ H := (by omega : M ≤ H).trans Nat.lt_two_pow_self.le
  have hM1 : M + 1 ≤ 2 ^ H := hH.trans Nat.lt_two_pow_self.le
  have hd : d ≤ 2 ^ H := (by dsimp [M] at hH; omega : d ≤ H).trans Nat.lt_two_pow_self.le
  have hg : g ≤ 2 ^ H := anchoredDictionaryBound_le N d
  have hP : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hcol : colBound M g ≤ 2 ^ 2 ^ (4 * H + 2) := by
    have h := (DeciNSSE.ElementaryBound.colBound_le_pow M g).trans
      (Nat.pow_le_pow_right (n := 2) (by decide) (show
        2 * M * (M + 1) * g + g ^ 2 + (M + 1) ^ 2 * g ^ 2 ≤ 4 * (2 ^ H) ^ 4 by
        calc
          _ ≤ 2 * (2 ^ H) * (2 ^ H) * (2 ^ H) + (2 ^ H) ^ 2 +
              (2 ^ H) ^ 2 * (2 ^ H) ^ 2 := by gcongr
          _ = 2 * (2 ^ H) ^ 3 + (2 ^ H) ^ 2 + (2 ^ H) ^ 4 := by ring
          _ ≤ 2 * (2 ^ H) ^ 4 + (2 ^ H) ^ 4 + (2 ^ H) ^ 4 := by
            exact Nat.add_le_add (Nat.add_le_add
              (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hP (by decide : 3 ≤ 4)))
              (Nat.pow_le_pow_right hP (by decide : 2 ≤ 4))) le_rfl
          _ = 4 * (2 ^ H) ^ 4 := by ring))
    have he : 4 * (2 ^ H) ^ 4 = 2 ^ (4 * H + 2) := by
      rw [← pow_mul, show H * 4 = 4 * H by omega, pow_add]
      simp only [show (2 : ℕ) ^ 2 = 4 from rfl]
      omega
    rwa [he] at h
  have hpow : ((2 ^ M) ^ (M + 1)) ^ g ≤ 2 ^ 2 ^ (4 * H + 2) := by
    rw [← pow_mul, ← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    calc
      M * ((M + 1) * g) ≤ 2 ^ H * (2 ^ H * 2 ^ H) := by gcongr
      _ = 2 ^ (3 * H) := by ring
      _ ≤ 2 ^ (4 * H + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 3 ^ g ≤ 2 ^ 2 ^ (4 * H + 2) := by
    have h2g : 2 * g ≤ 2 ^ (4 * H + 2) := by
      have h1 : 2 ^ (H + 1) ≤ 2 ^ (4 * H + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ] at h1
      omega
    calc
      3 ^ g ≤ 4 ^ g := Nat.pow_le_pow_left (by decide) g
      _ = 2 ^ (2 * g) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ 2 ^ (4 * H + 2) := Nat.pow_le_pow_right (by decide) h2g
  have hpcol : pcolBound M g ≤ 2 ^ 2 ^ (4 * H + 5) := by
    unfold pcolBound
    calc
      _ ≤ 2 ^ 2 ^ (4 * H + 2) * 2 ^ 2 ^ (4 * H + 2) * 2 ^ 2 ^ (4 * H + 2) *
          2 ^ 2 ^ (4 * H + 2) * 2 ^ 2 ^ (4 * H + 2) := by gcongr
      _ = 2 ^ (2 ^ (4 * H + 2) * 5) := by rw [pow_mul]; ring
      _ ≤ 2 ^ 2 ^ (4 * H + 5) := by
        apply Nat.pow_le_pow_right (by decide)
        have he : 2 ^ (4 * H + 5) = 2 ^ (4 * H + 2) * 8 := by
          rw [show 4 * H + 5 = 4 * H + 2 + 3 by omega, pow_add]
          norm_num
        omega
  have h3M : 3 * M ≤ 2 ^ (H + 2) := by
    have he : 2 ^ (H + 2) = 4 * 2 ^ H := by rw [pow_add]; ring
    omega
  unfold anchoredLengthBound posDescentFactor
  change 3 * M * pcolBound M g ^ d ≤ _
  calc
    _ ≤ 2 ^ (H + 2) * (2 ^ 2 ^ (4 * H + 5)) ^ d := by gcongr
    _ = 2 ^ (H + 2 + 2 ^ (4 * H + 5) * d) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ 2 ^ (5 * H + 6) := by
      apply Nat.pow_le_pow_right (by decide)
      have hp : H + 2 ≤ 2 ^ (5 * H + 5) :=
        (Nat.lt_two_pow_self (n := H + 2)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
      have hm : 2 ^ (4 * H + 5) * d ≤ 2 ^ (4 * H + 5) * 2 ^ H := Nat.mul_le_mul_left _ hd
      have he : 2 ^ (4 * H + 5) * 2 ^ H = 2 ^ (5 * H + 5) := by
        rw [← pow_add, show 4 * H + 5 + H = 5 * H + 5 by omega]
      have he' : 2 ^ (5 * H + 6) = 2 ^ (5 * H + 5) * 2 := pow_succ 2 (5 * H + 5)
      omega

end DeciENSSE.Anchored
