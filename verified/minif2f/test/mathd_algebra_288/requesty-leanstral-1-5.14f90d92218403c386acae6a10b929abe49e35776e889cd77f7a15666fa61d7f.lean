import Mathlib

open scoped Nat
open scoped Real

/--
A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? -/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  rcases h₀ with ⟨hx_lt, hy_lt⟩
  have hy_eq : y = -6 := by
    have hy_abs : abs y = -y := abs_of_neg hy_lt
    linarith
  have h₂sq : (x - 8)^2 + (y - 3)^2 = 225 := by
    have h_nonneg : 0 ≤ (x - 8)^2 + (y - 3)^2 := by positivity
    calc
      (x - 8)^2 + (y - 3)^2 = (Real.sqrt ((x - 8)^2 + (y - 3)^2))^2 := by
        symm; exact Real.sq_sqrt h_nonneg
      _ = 15^2 := by rw [h₂]
      _ = 225 := by norm_num
  rw [hy_eq] at h₂sq
  have hx_eq : x = -4 := by
    nlinarith
  have h_sq_eq : x^2 + y^2 = (n : ℝ) := by
    have h_nonneg_sum : 0 ≤ x^2 + y^2 := by positivity
    have h_nonneg_n : 0 ≤ (n : ℝ) := NNReal.coe_nonneg _
    calc
      x^2 + y^2 = (Real.sqrt (x^2 + y^2))^2 := by
        symm; exact Real.sq_sqrt h_nonneg_sum
      _ = (Real.sqrt (n : ℝ))^2 := by rw [h₃]
      _ = (n : ℝ) := Real.sq_sqrt h_nonneg_n
  rw [hx_eq, hy_eq] at h_sq_eq
  have h_eq : (52 : ℝ) = (n : ℝ) := by
    nlinarith
  exact_mod_cast h_eq.symm
