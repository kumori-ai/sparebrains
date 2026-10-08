import Mathlib

open scoped Nat
open scoped Real

/--
The expression $10x^2-x-24$ can be written as $(Ax-8)(Bx+3),$ where $A$ and $B$ are integers. What is $AB + B$? -/
theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by
  have h1 : a * b + 3 * a - 8 * b = 9 := by
    have h : ((a * b + 3 * a - 8 * b : ℤ) : ℝ) = 9 := by
      push_cast
      linear_combination (-1 : ℝ) * h₀ 1
    exact_mod_cast h
  have h2 : a * b - 3 * a + 8 * b = 11 := by
    have h : ((a * b - 3 * a + 8 * b : ℤ) : ℝ) = 11 := by
      push_cast
      linear_combination (-1 : ℝ) * h₀ (-1)
    exact_mod_cast h
  have hab : a * b = 10 := by linarith
  have hlin : 3 * a = 8 * b - 1 := by linarith
  have h3 : (b - 2) * (8 * b + 15) = 0 := by linear_combination (-b) * hlin + 3 * hab
  have hb : b = 2 := by
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · omega
  subst hb
  have ha : a = 5 := by linarith
  subst ha
  norm_num
