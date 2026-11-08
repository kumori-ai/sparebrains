import Mathlib

open scoped Nat
open scoped Real

/-- Find $3x^2 y^2$ if $x$ and $y$ are integers such that $y^2 + 3x^2 y^2 = 30x^2 + 517$. -/
theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by
  have hprod : (3 * x ^ 2 + 1) * (y ^ 2 - 10) = 507 := by
    linear_combination h₀
  have hA_pos : (0 : ℤ) < 3 * x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hB_pos : (0 : ℤ) < y ^ 2 - 10 := by
    by_contra h
    push_neg at h
    have hle : (3 * x ^ 2 + 1) * (y ^ 2 - 10) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA_pos) h
    omega
  have hB_ge : (1 : ℤ) ≤ y ^ 2 - 10 := by omega
  have hA_le : 3 * x ^ 2 + 1 ≤ 507 := by
    calc 3 * x ^ 2 + 1 = (3 * x ^ 2 + 1) * 1 := by ring
      _ ≤ (3 * x ^ 2 + 1) * (y ^ 2 - 10) :=
        mul_le_mul_of_nonneg_left hB_ge (le_of_lt hA_pos)
      _ = 507 := hprod
  have hB_le : y ^ 2 - 10 ≤ 507 := by
    calc y ^ 2 - 10 = (y ^ 2 - 10) * 1 := by ring
      _ ≤ (y ^ 2 - 10) * (3 * x ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ 3 * x ^ 2 + 1 by omega) (by omega)
      _ = 507 := by rw [mul_comm]; exact hprod
  have hx_sq : x ^ 2 ≤ 168 := by omega
  have hy_sq : y ^ 2 ≤ 517 := by omega
  have hx_lo : -12 ≤ x := by
    by_contra h
    push_neg at h
    have h1 : x ≤ -13 := by omega
    have h2 : (169 : ℤ) ≤ x ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -x - 13 by omega)
        (show (0 : ℤ) ≤ -x + 13 by omega)]
    omega
  have hx_hi : x ≤ 12 := by
    by_contra h
    push_neg at h
    have h1 : (13 : ℤ) ≤ x := by omega
    have h2 : (169 : ℤ) ≤ x ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ x - 13 by omega)
        (show (0 : ℤ) ≤ x + 13 by omega)]
    omega
  have hy_lo : -22 ≤ y := by
    by_contra h
    push_neg at h
    have h1 : y ≤ -23 := by omega
    have h2 : (529 : ℤ) ≤ y ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -y - 23 by omega)
        (show (0 : ℤ) ≤ -y + 23 by omega)]
    omega
  have hy_hi : y ≤ 22 := by
    by_contra h
    push_neg at h
    have h1 : (23 : ℤ) ≤ y := by omega
    have h2 : (529 : ℤ) ≤ y ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ y - 23 by omega)
        (show (0 : ℤ) ≤ y + 23 by omega)]
    omega
  have hy_ne : y ^ 2 ≠ 517 := by
    intro h
    interval_cases y <;> norm_num at h
  interval_cases x <;> omega
