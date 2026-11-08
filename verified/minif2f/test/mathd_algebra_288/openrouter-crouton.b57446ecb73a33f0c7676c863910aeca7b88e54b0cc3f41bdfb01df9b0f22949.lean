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
    have h := abs_of_neg hy
    rw [h] at h₁
    linarith
  have h2sq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ (x - 8) ^ 2 + (y - 3) ^ 2 by positivity)
    rw [h₂] at h
    norm_num at h
    linarith
  have hsq : (x - 8) ^ 2 = 144 := by
    rw [hy_eq] at h2sq
    norm_num at h2sq
    linarith
  have hx_eq : x = -4 := by
    have hfact : (x - 8 - 12) * (x - 8 + 12) = 0 := by
      have h : (x - 8 - 12) * (x - 8 + 12) = (x - 8) ^ 2 - 144 := by ring
      rw [h, hsq]
      norm_num
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      linarith
    · linarith
  have hsum : x ^ 2 + y ^ 2 = 52 := by
    rw [hx_eq, hy_eq]
    norm_num
  have hn_real : (n : ℝ) = 52 := by
    have h1' := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + y ^ 2 by positivity)
    have h2' := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
    rw [h₃] at h1'
    rw [h2'] at h1'
    rw [hsum] at h1'
    exact h1'
  exact_mod_cast hn_real
