import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  rcases h₀ with ⟨hx_neg, hy_neg⟩
  have hy : y = -6 := by
    rw [abs_of_neg hy_neg] at h₁
    linarith
  have h_nonneg_sq : 0 ≤ (x - 8) ^ 2 + (y - 3) ^ 2 := by positivity
  have h₂_sq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    calc
      (x - 8) ^ 2 + (y - 3) ^ 2 = (Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt h_nonneg_sq]
      _ = 15 ^ 2 := by rw [h₂]
      _ = 225 := by norm_num
  rw [hy] at h₂_sq
  have hx_minus_8_sq_eq : (x - 8) ^ 2 = 144 := by nlinarith
  have hx_minus_8_neg : x - 8 < 0 := by linarith
  have hx_minus_8_eq : x - 8 = -12 := by
    nlinarith
  have hx : x = -4 := by linarith
  have h_sum_sq : x ^ 2 + y ^ 2 = 52 := by
    rw [hx, hy]
    norm_num
  have h_nonneg_sum_sq : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have h_nonneg_n : 0 ≤ (n : ℝ) := NNReal.coe_nonneg _
  have h_eq_real : x ^ 2 + y ^ 2 = (n : ℝ) :=
    (Real.sqrt_inj h_nonneg_sum_sq h_nonneg_n).mp h₃
  have h_n_eq_52_real : (n : ℝ) = 52 :=
    h_eq_real.symm.trans h_sum_sq
  exact_mod_cast h_n_eq_52_real
