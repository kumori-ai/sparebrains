import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  rcases h₀ with ⟨hx_neg, hy_neg⟩
  have hy_eq : y = -6 := by
    have h_abs_neg : abs y = -y := abs_of_neg hy_neg
    rw [h_abs_neg] at h₁
    linarith
  have h_nonneg_sq : 0 ≤ (x - 8) ^ 2 + (y - 3) ^ 2 := by positivity
  have h_sq_eq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    have h_sq := congrArg (fun t => t ^ 2) h₂
    rw [Real.sq_sqrt h_nonneg_sq] at h_sq
    norm_num at h_sq
    exact h_sq
  rw [hy_eq] at h_sq_eq
  norm_num at h_sq_eq
  have h_factor : (x - 20) * (x + 4) = 0 := by
    nlinarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with hx20 | hx4
  · have hx : x = 20 := by linarith
    linarith
  · have hx : x = -4 := by linarith
    have h_sum_sq : x ^ 2 + y ^ 2 = 52 := by
      rw [hx, hy_eq]
      norm_num
    have hn_nonneg : 0 ≤ (n : ℝ) := NNReal.coe_nonneg _
    have h52_nonneg : 0 ≤ (52 : ℝ) := by norm_num
    have h_sqrt_eq : Real.sqrt (52 : ℝ) = Real.sqrt (n : ℝ) := by
      rw [← h_sum_sq, h₃]
    have h_eq_real : (52 : ℝ) = (n : ℝ) :=
      (Real.sqrt_inj h52_nonneg hn_nonneg).mp h_sqrt_eq
    exact_mod_cast h_eq_real.symm
