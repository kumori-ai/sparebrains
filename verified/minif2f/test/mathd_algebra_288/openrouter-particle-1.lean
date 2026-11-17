import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have hy : y = -6 := by
    rw [abs_of_neg h₀.2] at h₁
    linarith
  have h2sq : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
    have h := congrArg (fun t : ℝ => t ^ 2) h₂
    rw [Real.sq_sqrt (by positivity : 0 ≤ (x - 8) ^ 2 + (y - 3) ^ 2)] at h
    norm_num at h
    exact h
  have hx_sq : (x - 8) ^ 2 = 144 := by
    have h := h2sq
    rw [hy] at h
    norm_num at h
    linarith
  have hx : x = -4 := by
    have h : (x - 8) ^ 2 = (12 : ℝ) ^ 2 := by
      norm_num
      exact hx_sq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · linarith [h₀.1]
    · linarith
  have hxy : x ^ 2 + y ^ 2 = 52 := by
    rw [hx, hy]
    norm_num
  have hsqrt : Real.sqrt (52 : ℝ) = Real.sqrt (n : ℝ) := by
    simpa [hxy] using h₃
  have hn : (n : ℝ) = 52 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hsqrt
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 52),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))] at h
    exact h.symm
  apply NNReal.coe_injective
  simpa using hn
