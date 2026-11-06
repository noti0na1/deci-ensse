import DeciENSSE.Bounds.Tower
import DeciENSSE.Anchored.Monotone
import DeciENSSE.Core.Words.Mortal.Bound
import DeciENSSE.Core.Words.Pump
import DeciNSSE.RejectedTail.Decision

/-! # Closed forms of the reader bounds

Estimates of the three length bounds of the decision procedure by explicit polynomials and
towers of exponentials:

- the hole bound `holeBound(N, d_N)` of a reader with the rejected-path property, at a
  power-of-two number of states (the closed form of `thm:un-decidable`);
- the non-mortal bound `Lnm(a, b, a', b') ≤ 54 a² b a' b'` (`sec:nm-three-cases`,
  `app:nm-three-cases`);
- the mortal bound `Len♯_I ≤ E₃(3α + 2β + 9)` (`lem:mo-estimate`).

All statements are about natural numbers; the state counts of the extracted readers are
substituted in `DeciENSSE.Bounds`.

## Main declarations

- `holeLengthBound_two_pow_le`: `holeBound(2^k, d_{2^k}) ≤ E₃(5k + 12)` for `k ≥ 3`.
- `pumpCapacity_le`, `pumpHoleBound_le_sharp`, `pumpHoleBound_le`: the estimates of `Pcap`
  and `Lnm`.
- `anchoredExponent_le`: `Ξ♯(N₀, D₀) ≤ 17 N₀ D₀²` for `8 ≤ N₀` and `2 N₀ ≤ D₀`.
- `mortalHoleBound_le_E3`: the mortal estimate `lem:mo-estimate`.

The declarations are in the namespace `DeciENSSE.Bounds`.
-/

namespace DeciENSSE.Bounds
open DeciENSSE.Anchored DeciENSSE.Core.Words DeciENSSE.Core.Words.Mortal DeciNSSE.RejectedTail

/-! ## The hole bound of a reader with the rejected-path property -/

/-- `1280 (N + 1)^5 < 2^12 N^5` for `N ≥ 8`, since `(9/8)^5 < 2`. -/
theorem holeExponent_lt {N : ℕ} (hN : 8 ≤ N) : 1280 * (N + 1) ^ 5 < 2 ^ 12 * N ^ 5 := by
  have h : (8 * (N + 1)) ^ 5 ≤ (9 * N) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hN5 : 0 < N ^ 5 := by positivity
  rw [mul_pow, mul_pow] at h
  norm_num at h ⊢
  linarith

/-- **Closed form of the hole bound** (`thm:un-decidable`, closed form): a reader with
`N = 2^k ≥ 8` states satisfies `holeBound(N, d_N) ≤ E₃(5k + 12)`, by
`holeBound(N, d_N) ≤ 2^2^(1280 (N + 1)^5)` and `1280 (N + 1)^5 < 2^12 N^5 = 2^(5k + 12)`. -/
theorem holeLengthBound_two_pow_le {k : ℕ} (hk : 3 ≤ k) :
    holeLengthBound (2 ^ k) ≤ E3 (5 * k + 12) := by
  refine (holeLengthBound_le _).trans (two_pow_two_pow_le_E3 ?_)
  have h8 : 8 ≤ 2 ^ k := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hk
  refine (holeExponent_lt h8).le.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_add]
  ring_nf

/-! ## The non-mortal bound `Lnm` -/

section Pump
variable {a b c d : ℕ}

/-- `Pcap(a, b, a', b') ≤ 5 a b a' b' + a² a'` for positive state counts
(`app:nm-three-cases`). -/
theorem pumpCapacity_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    pumpCapacity a b c d ≤ 5 * a * b * c * d + a ^ 2 * c := by
  have h1 : a * b * 1 * 1 ≤ a * b * c * d := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hc) hd
  have h2 : a * 1 * c * 1 ≤ a * b * c * d :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hb) le_rfl) hd
  have h3 : 1 * b * 1 * d ≤ a * b * c * d :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha le_rfl) hc) le_rfl
  unfold pumpCapacity
  nlinarith

/-- `Pcap(a, b, a', b') ≤ 6 a² b a' b'` for positive state counts (`app:nm-three-cases`). -/
theorem pumpCapacity_le_sq (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    pumpCapacity a b c d ≤ 6 * a ^ 2 * b * c * d := by
  have h1 : a * b * c * d * 1 ≤ a * b * c * d * a := Nat.mul_le_mul le_rfl ha
  have h2 : a ^ 2 * 1 * c * 1 ≤ a ^ 2 * b * c * d :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hb) le_rfl) hd
  have := pumpCapacity_le ha hb hc hd
  nlinarith

/-- `Lnm(a, b, a', b') ≤ 48 a b a' b' + 4 a² a' + 6 a` for positive state counts
(`app:nm-three-cases`). -/
theorem pumpHoleBound_le_sharp (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    pumpHoleBound a b c d ≤ 48 * a * b * c * d + 4 * a ^ 2 * c + 6 * a := by
  have hP := pumpCapacity_le ha hb hc hd
  have hm : max (12 * a * b * c * d) (pumpCapacity a b c d) ≤
      12 * a * b * c * d + a ^ 2 * c :=
    max_le (Nat.le_add_right _ _) (hP.trans (by have := Nat.zero_le (a * b * c * d); linarith))
  change 4 * max _ _ + 6 * a ≤ _
  nlinarith

/-- **The non-mortal bound is polynomial** (`sec:nm-three-cases`, `app:nm-three-cases`):
`Lnm(a, b, a', b') ≤ 48 a² b a' b' + 6 a ≤ 54 a² b a' b'` for positive state counts. -/
theorem pumpHoleBound_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    pumpHoleBound a b c d ≤ 48 * a ^ 2 * b * c * d + 6 * a ∧
      48 * a ^ 2 * b * c * d + 6 * a ≤ 54 * a ^ 2 * b * c * d := by
  have hP := pumpCapacity_le_sq ha hb hc hd
  have h1 : a * b * c * d * 1 ≤ a * b * c * d * a := Nat.mul_le_mul le_rfl ha
  have h2 : a * 1 * 1 * 1 * 1 ≤ a * a * b * c * d :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl ha) hb) hc) hd
  have hm : max (12 * a * b * c * d) (pumpCapacity a b c d) ≤ 12 * a ^ 2 * b * c * d :=
    max_le (by nlinarith) (hP.trans (by nlinarith))
  change 4 * max _ _ + 6 * a ≤ _ ∧ _
  constructor <;> nlinarith

end Pump

/-! ## The mortal bound -/

/-- The exponent estimate of `lem:mo-estimate`: `Ξ♯(N₀, D₀) ≤ 17 N₀ D₀²` for `N₀ ≥ 8` and
`2 N₀ ≤ D₀` (hence `D₀ ≥ 16`). -/
theorem anchoredExponent_le {N D : ℕ} (hN : 8 ≤ N) (hND : 2 * N ≤ D) :
    anchoredExponent N D ≤ 17 * N * D ^ 2 := by
  have hD : 16 ≤ D := by omega
  -- `10 N (N + D)(D + 1) ≤ 10 N · (3/2) D · (17/16) D`
  have h1 : 2 * (N + D) * (16 * (D + 1)) ≤ 3 * D * (17 * D) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1' : N * (2 * (N + D) * (16 * (D + 1))) ≤ N * (3 * D * (17 * D)) :=
    Nat.mul_le_mul_left N h1
  -- `6 N² ≤ 3 N D ≤ (3/16) N D²`
  have h2 : 3 * N * (2 * N) ≤ 3 * N * D := Nat.mul_le_mul_left _ hND
  have h3 : N * D * 16 ≤ N * D * D := Nat.mul_le_mul_left _ hD
  -- `7 N + 3 D + 4 ≤ N D`
  have h4 : 8 * D ≤ N * D := Nat.mul_le_mul_right D hN
  unfold anchoredExponent
  nlinarith

/-- **Mortal bound** (`lem:mo-estimate`). If the Π-reader of an instance with state counts
`a, b, c, d` (the paper's `N_A, N_B, N_{A'}, N_{B'}`) has `N_I = 1 + ac + bd + ad ≤ 2^α`
states, with `α ≥ 3`, and `N_A = a ≤ 2^β`, then `Len♯_I ≤ E₃(3α + 2β + 9)`. The proof
follows the paper: monotonicity replaces `N_I` and `d_I = 2 N_I a - 1` by `N₀ = 2^α` and
`D₀ = 2^(α+β+1)`, and the closed form `Len♯(N₀, D₀) ≤ 2^2^(5 Ξ♯(N₀, D₀) + 6)` applies. -/
theorem mortalHoleBound_le_E3 {a b c d α β : ℕ} (hα : 3 ≤ α)
    (hN : 1 + a * c + b * d + a * d ≤ 2 ^ α) (ha : a ≤ 2 ^ β) :
    mortalHoleBound a b c d ≤ E3 (3 * α + 2 * β + 9) := by
  have hdI : 2 * (1 + a * c + b * d + a * d) * a - 1 ≤ 2 ^ (α + β + 1) := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN) ha
    rw [show 2 ^ (α + β + 1) = 2 * 2 ^ α * 2 ^ β by rw [pow_succ, pow_add]; ring]
    omega
  have h8 : 8 ≤ 2 ^ α := by simpa using Nat.pow_le_pow_right (n := 2) (by decide) hα
  have hND : 2 * 2 ^ α ≤ 2 ^ (α + β + 1) := by
    rw [pow_succ, pow_add, Nat.mul_comm _ 2]
    exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
  have hΞ := anchoredExponent_le h8 hND
  have hP : 1 ≤ 2 ^ (3 * α + 2 * β) := Nat.one_le_two_pow
  have he1 : 2 ^ α * (2 ^ (α + β + 1)) ^ 2 = 4 * 2 ^ (3 * α + 2 * β) := by
    rw [← pow_mul, ← pow_add, show (α + β + 1) * 2 = 2 * α + 2 * β + 2 by ring,
      show α + (2 * α + 2 * β + 2) = 3 * α + 2 * β + 2 by ring, pow_add]
    ring
  have he2 : 2 ^ (3 * α + 2 * β + 9) = 512 * 2 ^ (3 * α + 2 * β) := by
    rw [pow_add]; ring
  calc mortalHoleBound a b c d
      = anchoredLengthBound (1 + a * c + b * d + a * d)
          (2 * (1 + a * c + b * d + a * d) * a - 1) := rfl
    _ ≤ anchoredLengthBound (2 ^ α) (2 ^ (α + β + 1)) := anchoredLengthBound_mono hN hdI
    _ ≤ 2 ^ 2 ^ (5 * anchoredExponent (2 ^ α) (2 ^ (α + β + 1)) + 6) :=
        anchoredLengthBound_le _ _
    _ ≤ E3 (3 * α + 2 * β + 9) := by
        apply two_pow_two_pow_le_E3
        rw [he2]
        have : 17 * 2 ^ α * (2 ^ (α + β + 1)) ^ 2 = 68 * 2 ^ (3 * α + 2 * β) := by
          rw [Nat.mul_assoc, he1]; ring
        omega

/-! ## The state counts of the extracted instances

The extracted instances have the state counts `N_A = 2^(2v)`, `N_B = 2^(2v+2s+1)` and
`N_{A'} = N_{B'} = 2^(2s)` (`DeciENSSE.Bounds.extractedBoundSelf_eq`). Here `v` and `s` are
arbitrary numbers. -/

section Extracted
variable (v s : ℕ)

/-- The Π-reader count at the extracted state counts:
`N_I = 1 + 2^(2v+2s+1) + 2^(2v+4s+1)` (`cor:mo-extracted`). -/
theorem piStates_eq :
    1 + 2 ^ (2 * v) * 2 ^ (2 * s) + 2 ^ (2 * v + 2 * s + 1) * 2 ^ (2 * s) +
        2 ^ (2 * v) * 2 ^ (2 * s) =
      1 + 2 ^ (2 * v + 2 * s + 1) + 2 ^ (2 * v + 4 * s + 1) := by
  ring

variable {v s}

/-- `N_I ≤ 2^(2v+4s+2)` for `s ≥ 1` (`cor:mo-extracted`). -/
theorem piStates_le (hs : 1 ≤ s) :
    1 + 2 ^ (2 * v + 2 * s + 1) + 2 ^ (2 * v + 4 * s + 1) ≤ 2 ^ (2 * v + 4 * s + 2) := by
  have h4 : 4 * 2 ^ (2 * v + 2 * s + 1) ≤ 2 ^ (2 * v + 4 * s + 1) := by
    rw [show 4 * 2 ^ (2 * v + 2 * s + 1) = 2 ^ (2 * v + 2 * s + 3) by ring]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h1 : 1 ≤ 2 ^ (2 * v + 2 * s + 1) := Nat.one_le_two_pow
  rw [show 2 ^ (2 * v + 4 * s + 2) = 2 * 2 ^ (2 * v + 4 * s + 1) by ring]
  omega

/-- The mortal bound at the extracted state counts: `Len♯ ≤ E₃(10v + 12s + 15)` for `s ≥ 1`,
by `lem:mo-estimate` with `α = 2v + 4s + 2` and `β = 2v` (`cor:mo-extracted`). -/
theorem mortalHoleBound_extracted_le (hs : 1 ≤ s) :
    mortalHoleBound (2 ^ (2 * v)) (2 ^ (2 * v + 2 * s + 1)) (2 ^ (2 * s)) (2 ^ (2 * s)) ≤
      E3 (10 * v + 12 * s + 15) := by
  have h := mortalHoleBound_le_E3 (a := 2 ^ (2 * v)) (b := 2 ^ (2 * v + 2 * s + 1))
    (c := 2 ^ (2 * s)) (d := 2 ^ (2 * s)) (α := 2 * v + 4 * s + 2) (β := 2 * v) (by omega)
    ((piStates_eq v s).le.trans (piStates_le hs)) le_rfl
  rwa [show 3 * (2 * v + 4 * s + 2) + 2 * (2 * v) + 9 = 10 * v + 12 * s + 15 by ring] at h

/-- The non-mortal bound at the extracted state counts:
`Lnm ≤ 54 N_A² N_B N_{A'} N_{B'} = 54 · 2^(6v+6s+1)` (`prop:as-bounds`). -/
theorem pumpHoleBound_extracted_le :
    pumpHoleBound (2 ^ (2 * v)) (2 ^ (2 * v + 2 * s + 1)) (2 ^ (2 * s)) (2 ^ (2 * s)) ≤
      54 * 2 ^ (6 * v + 6 * s + 1) := by
  have h := (pumpHoleBound_le Nat.one_le_two_pow Nat.one_le_two_pow Nat.one_le_two_pow
    Nat.one_le_two_pow (a := 2 ^ (2 * v)) (b := 2 ^ (2 * v + 2 * s + 1)) (c := 2 ^ (2 * s))
    (d := 2 ^ (2 * s)))
  refine (h.1.trans h.2).trans (le_of_eq ?_)
  ring

/-- A non-mortal hole word at the extracted state counts has length at most
`Lnm + 1 < 2^(6v+6s+7)`, a single exponential (`prop:as-bounds`). -/
theorem pumpHoleBound_extracted_lt :
    pumpHoleBound (2 ^ (2 * v)) (2 ^ (2 * v + 2 * s + 1)) (2 ^ (2 * s)) (2 ^ (2 * s)) + 1 <
      2 ^ (6 * v + 6 * s + 7) := by
  have h := pumpHoleBound_extracted_le (v := v) (s := s)
  have h1 : 1 ≤ 2 ^ (6 * v + 6 * s + 1) := Nat.one_le_two_pow
  rw [show 2 ^ (6 * v + 6 * s + 7) = 64 * 2 ^ (6 * v + 6 * s + 1) by ring]
  omega

end Extracted

end DeciENSSE.Bounds
