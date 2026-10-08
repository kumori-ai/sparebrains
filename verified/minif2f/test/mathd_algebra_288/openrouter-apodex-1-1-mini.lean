import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have hy : y = -6 := by
    have hy' : y < 0 := h₀.2
    rw [abs_of_neg hy'] at h₁
    linarith
  have hx : x = -4 := by
    have h₂' : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
      have h₂'' : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) ^ 2 = 15 ^ 2 := by rw [h₂]
      have h₂''' : 0 ≤ (x - 8) ^ 2 + (y - 3) ^ 2 := by positivity
      rw [Real.sq_sqrt h₂'''] at h₂''
      norm_num at h₂'' ⊢
      exact h₂''
    rw [hy] at h₂'
    norm_num at h₂'
    have h₄ : (x - 8) ^ 2 = 12 ^ 2 := by
      norm_num at h₂' ⊢
      linarith
    nlinarith
  have h₄ : x ^ 2 + y ^ 2 = 52 := by
    rw [hx, hy]
    norm_num
  have h₅ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt 52 := by rw [h₄]
  have h₆ : Real.sqrt n = Real.sqrt 52 := by
    rw [← h₃, h₅]
  have h₇ : (n : ℝ) = 52 := by
    apply (Real.sqrt_inj (NNReal.coe_nonneg n) (by norm_num)).mp
    rw [h₆]
  exact_mod_cast h₇
