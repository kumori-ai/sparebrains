import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h₂_nat : x + y = 36 := by
    have h₂int : (x : ℤ) + (y : ℤ) = 36 := by
      norm_num at h₂
      omega
    exact_mod_cast h₂int
  have hsum : x + 5 * x = 36 := by
    rw [h₁]
    exact h₂_nat
  have h6 : 6 * x = 36 := by
    calc
      6 * x = x + 5 * x := by ring
      _ = 36 := hsum
  have : x = 6 := by
    omega
  exact this
