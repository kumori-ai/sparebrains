import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x ≤ 1
    · exact ⟨hx, hx1⟩
    · have h1 : 1 < x := lt_of_not_ge hx1
      have hxm1 : 0 ≤ x - 1 := by linarith
      have hxp1 : 0 ≤ x + 1 := by linarith
      rw [abs_of_nonneg hxm1, abs_of_nonneg hx, abs_of_nonneg hxp1] at h₀
      linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    have hxm1 : x - 1 < 0 := by linarith
    by_cases hxp1 : x + 1 ≤ 0
    · rw [abs_of_neg hxm1, abs_of_neg hx', abs_of_nonpos hxp1] at h₀
      linarith
    · have hxp1' : 0 < x + 1 := lt_of_not_ge hxp1
      rw [abs_of_neg hxm1, abs_of_neg hx', abs_of_nonneg (le_of_lt hxp1')] at h₀
      linarith
