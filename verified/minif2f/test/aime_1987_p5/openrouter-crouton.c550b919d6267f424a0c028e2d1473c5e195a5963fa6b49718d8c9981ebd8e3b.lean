import Mathlib

open scoped Nat
open scoped Real

/-- Find $3x^2 y^2$ if $x$ and $y$ are integers such that $y^2 + 3x^2 y^2 = 30x^2 + 517$. -/
theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have h1 : (3 * x ^ 2 + 1) * (3 * y ^ 2 - 30) = 1521 := by
    linear_combination 3 * h₀
  have hx_pos : 0 < 3 * x ^ 2 + 1 := by
    have h := sq_nonneg x
    linarith
  have hy_pos : 0 < 3 * y ^ 2 - 30 := by
    have hpos : 0 < (3 * x ^ 2 + 1) * (3 * y ^ 2 - 30) := by
      rw [h1]
      norm_num
    rcases mul_pos_iff.mp hpos with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · linarith
  have hB3 : 3 <= 3 * y ^ 2 - 30 := by
    have h1' : 0 < y ^ 2 - 10 := by linarith
    have h2' : 1 <= y ^ 2 - 10 := by omega
    linarith
  have hA_le : 3 * x ^ 2 + 1 <= 507 := by
    have h := mul_le_mul_of_nonneg_left hB3 (le_of_lt hx_pos)
    rw [h1] at h
    linarith
  have hx_sq : x ^ 2 <= 168 := by omega
  have hx_abs : |x| < 13 := by
    have h : x ^ 2 < (13 : ℤ) ^ 2 := by
      have h13 : (13 : ℤ) ^ 2 = 169 := by norm_num
      linarith
    exact abs_lt_of_sq_lt_sq h (by norm_num)
  have hy_sq : y ^ 2 <= 517 := by
    have hA1 : (1 : ℤ) <= 3 * x ^ 2 + 1 := by
      have h := sq_nonneg x
      linarith
    have h := mul_le_mul_of_nonneg_right hA1 (le_of_lt hy_pos)
    rw [h1] at h
    omega
  have hy_abs : |y| < 23 := by
    have h : y ^ 2 < (23 : ℤ) ^ 2 := by
      have h23 : (23 : ℤ) ^ 2 = 529 := by norm_num
      linarith
    exact abs_lt_of_sq_lt_sq h (by norm_num)
  have hx_lo : -13 < x := (abs_lt.mp hx_abs).1
  have hx_hi : x < 13 := (abs_lt.mp hx_abs).2
  have hy_lo : -23 < y := (abs_lt.mp hy_abs).1
  have hy_hi : y < 23 := (abs_lt.mp hy_abs).2
  interval_cases x <;> norm_num at h₀ ⊢ <;> first | omega | (interval_cases y <;> omega)
