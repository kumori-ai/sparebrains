import Mathlib

open scoped Nat
open scoped Real

/--
Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  have hsum : x + y = 14 := by
    linarith
  have hpos : 0 < x * y := by
    have hsqrtpos : 0 < Real.sqrt (x * y) := by
      rw [h₁]
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 19)
    exact (Real.sqrt_pos.mp hsqrtpos)
  have hxy : x * y = 19 := by
    have hnonneg : 0 ≤ x * y := le_of_lt hpos
    have h19nonneg : 0 ≤ (19 : ℝ) := by norm_num
    exact (Real.sqrt_inj hnonneg h19nonneg).mp h₁
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 14 ^ 2 - 2 * 19 := by rw [hsum, hxy]
    _ = 158 := by norm_num
