import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  obtain ⟨hx, hy⟩ := h₀
  have hy_eq : y = -6 := by
    rw [abs_of_neg hy] at h₁
    linarith
  have h_nonneg : 0 ≤ (x - 8) ^ 2 + (y - 3) ^ 2 := by positivity
  have h_sq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    have h : (Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2)) ^ 2 = (15 : ℝ) ^ 2 := by rw [h₂]
    rw [Real.sq_sqrt h_nonneg] at h
    have h15 : (15 : ℝ) ^ 2 = 225 := by norm_num
    rw [h15] at h
    exact h
  have h144 : (x - 8) ^ 2 = 144 := by
    rw [hy_eq] at h_sq
    have h81 : (-6 - 3 : ℝ) ^ 2 = 81 := by norm_num
    rw [h81] at h_sq
    linarith
  have hx_eq : x = -4 := by
    have hprod : ((x - 8) - 12) * ((x - 8) + 12) = 0 := by
      have heq : ((x - 8) - 12) * ((x - 8) + 12) = (x - 8) ^ 2 - 144 := by ring
      rw [heq, h144]
      norm_num
    rcases mul_eq_zero.mp hprod with h | h
    · have hx20 : x = 20 := by linarith
      rw [hx20] at hx
      norm_num at hx
    · have hx4 : x = -4 := by linarith
      exact hx4
  have h_left : x ^ 2 + y ^ 2 = 52 := by
    rw [hx_eq, hy_eq]
    norm_num
  have h_sq3 : x ^ 2 + y ^ 2 = (n : ℝ) := by
    have h : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = (Real.sqrt (n : ℝ)) ^ 2 := by rw [h₃]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
    exact h
  have hn : (n : ℝ) = 52 := by linarith
  exact_mod_cast hn
