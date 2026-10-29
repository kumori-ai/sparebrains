import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have hsum_int : (x : ℤ) + (y : ℤ) = 36 := by
    linarith

  have hsum_nat : x + y = 36 := by
    exact_mod_cast hsum_int

  have hsum' : x + 5 * x = 36 := by
    rw [← h₁] at hsum_nat
    exact hsum_nat

  omega
