import Mathlib.Order.Monotone.Basic

/-! # The triple exponential of the counterexample bounds

The counterexample bounds in the number of variables are stated with
`E₃(x) = 2 ^ 2 ^ 2 ^ x`. This file defines `E₃` and the comparisons the bounds use.

## Main declarations

- `E3`: the function `E₃`.
- `E3_le_E3`, `E3_strictMono`, `E3_le_E3_iff`: `E₃` is strictly increasing.
- `two_pow_two_pow_le_E3`: two exponentials over an exponent at most `2 ^ x` are at most
  `E₃(x)`.
- `two_pow_le_E3`: a single exponential `2 ^ x` is at most `E₃(x)`.

The declarations are in the namespace `DeciENSSE.Bounds`.
-/

namespace DeciENSSE.Bounds

/-- The triple exponential `E₃(x) = 2 ^ 2 ^ 2 ^ x`. -/
def E3 (x : ℕ) : ℕ := 2 ^ 2 ^ 2 ^ x

/-- `E₃` is nondecreasing. -/
theorem E3_le_E3 {x y : ℕ} (h : x ≤ y) : E3 x ≤ E3 y :=
  Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) h))

/-- `E₃` is monotone. -/
theorem E3_mono : Monotone E3 := fun _ _ => E3_le_E3

/-- `E₃` is strictly increasing. -/
theorem E3_strictMono : StrictMono E3 := fun _ _ h =>
  Nat.pow_lt_pow_right (by decide)
    (Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) h))

/-- `E₃(x) ≤ E₃(y)` exactly when `x ≤ y`. -/
theorem E3_le_E3_iff {x y : ℕ} : E3 x ≤ E3 y ↔ x ≤ y := E3_strictMono.le_iff_le

/-- Two exponentials over an exponent at most `2 ^ x` are at most `E₃(x)`. -/
theorem two_pow_two_pow_le_E3 {a x : ℕ} (h : a ≤ 2 ^ x) : 2 ^ 2 ^ a ≤ E3 x :=
  Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) h)

/-- A single exponential is at most `E₃`: `2 ^ x ≤ E₃(x)`. -/
theorem two_pow_le_E3 (x : ℕ) : 2 ^ x ≤ E3 x :=
  Nat.pow_le_pow_right (by decide)
    (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) Nat.lt_two_pow_self.le))

/-- Every number is below its triple exponential. -/
theorem lt_E3 (x : ℕ) : x < E3 x := Nat.lt_two_pow_self.trans_le (two_pow_le_E3 x)

end DeciENSSE.Bounds
