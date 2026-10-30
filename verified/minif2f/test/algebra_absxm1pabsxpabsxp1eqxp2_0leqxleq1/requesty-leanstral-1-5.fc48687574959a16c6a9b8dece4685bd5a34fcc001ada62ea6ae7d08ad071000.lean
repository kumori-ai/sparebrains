import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases hx : x ≤ -1
  · -- x ≤ -1
    have hx1' : x - 1 ≤ 0 := by linarith
    have hx0' : x ≤ 0 := by linarith
    have hx1'' : x + 1 ≤ 0 := by linarith
    have abs1 : abs (x - 1) = -(x - 1) := abs_of_nonpos hx1'
    have absx : abs x = -x := abs_of_nonpos hx0'
    have abs1' : abs (x + 1) = -(x + 1) := abs_of_nonpos hx1''
    rw [abs1, absx, abs1'] at h₀
    linarith
  · -- x > -1
    by_cases hx0 : x ≤ 0
    · -- -1 < x ≤ 0
      have hx1' : x - 1 ≤ 0 := by linarith
      have abs1 : abs (x - 1) = -(x - 1) := abs_of_nonpos hx1'
      have absx : abs x = -x := abs_of_nonpos hx0
      have hx1'' : x + 1 ≥ 0 := by linarith
      have abs1' : abs (x + 1) = x + 1 := abs_of_nonneg hx1''
      rw [abs1, absx, abs1'] at h₀
      have hx_eq : x = 0 := by linarith
      constructor <;> linarith
    · -- x > 0
      by_cases hx1 : x ≤ 1
      · -- 0 < x ≤ 1
        have hx0' : 0 ≤ x := by linarith
        exact ⟨hx0', hx1⟩
      · -- x > 1
        have hx1' : x - 1 ≥ 0 := by linarith
        have abs1 : abs (x - 1) = x - 1 := abs_of_nonneg hx1'
        have absx : abs x = x := abs_of_nonneg (by linarith)
        have hx1'' : x + 1 ≥ 0 := by linarith
        have abs1' : abs (x + 1) = x + 1 := abs_of_nonneg hx1''
        rw [abs1, absx, abs1'] at h₀
        have hx_eq : x = 1 := by linarith
        constructor <;> linarith
