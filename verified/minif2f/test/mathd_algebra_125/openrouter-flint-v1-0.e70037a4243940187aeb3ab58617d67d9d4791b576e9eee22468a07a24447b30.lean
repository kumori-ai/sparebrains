import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h₁_int : (5 : ℤ) * (x : ℤ) = (y : ℤ) := by
    exact_mod_cast h₁
  have h_age : (x : ℤ) + (y : ℤ) = 36 := by
    nlinarith [h₂]
  have h_mul : (6 : ℤ) * (x : ℤ) = 36 := by
    nlinarith [h₁_int, h_age]
  have hx_int : (x : ℤ) = 6 := by
    nlinarith
  exact_mod_cast hx_int
