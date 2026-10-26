import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  by_cases hx1 : x ≤ -1
  · -- x ≤ -1
    have hx1' : x - 1 ≤ 0 := by linarith
    have hx0' : x ≤ 0 := by linarith
    have hxp1' : x + 1 ≤ 0 := by linarith
    have abs1 : abs (x - 1) = -(x - 1) := abs_of_nonpos hx1'
    have absx : abs x = -x := abs_of_nonpos hx0'
    have absxp1 : abs (x + 1) = -(x + 1) := abs_of_nonpos hxp1'
    rw [abs1, absx, absxp1] at h₀
    ring_nf at h₀
    exfalso; linarith
  · -- not x ≤ -1, so -1 < x
    by_cases hx0 : x ≤ 0
    · -- -1 < x ≤ 0
      have hx1' : x - 1 ≤ 0 := by linarith
      have hxp1' : 0 ≤ x + 1 := by linarith
      have abs1 : abs (x - 1) = -(x - 1) := abs_of_nonpos hx1'
      have absx : abs x = -x := abs_of_nonpos hx0
      have absxp1 : abs (x + 1) = x + 1 := abs_of_nonneg hxp1'
      rw [abs1, absx, absxp1] at h₀
      ring_nf at h₀
      -- h₀: 2 - x = x + 2 → x = 0
      have hx0_eq : x = 0 := by linarith
      constructor; linarith; linarith
    · -- not x ≤ 0, so 0 < x
      have hx0_nonneg : 0 ≤ x := by linarith
      by_cases hx1' : x ≤ 1
      · -- 0 < x ≤ 1
        have hx1'' : x - 1 ≤ 0 := by linarith
        have hxp1' : 0 ≤ x + 1 := by linarith
        have abs1 : abs (x - 1) = -(x - 1) := abs_of_nonpos hx1''
        have absx : abs x = x := abs_of_nonneg hx0_nonneg
        have absxp1 : abs (x + 1) = x + 1 := abs_of_nonneg hxp1'
        rw [abs1, absx, absxp1] at h₀
        ring_nf at h₀
        -- h₀: 2 + x = x + 2, trivial
        constructor; exact hx0_nonneg; exact hx1'
      · -- x > 1
        have hx1'' : 0 ≤ x - 1 := by linarith
        have hxp1' : 0 ≤ x + 1 := by linarith
        have abs1 : abs (x - 1) = x - 1 := abs_of_nonneg hx1''
        have absx : abs x = x := abs_of_nonneg hx0_nonneg
        have absxp1 : abs (x + 1) = x + 1 := abs_of_nonneg hxp1'
        rw [abs1, absx, absxp1] at h₀
        ring_nf at h₀
        -- h₀: 3*x = x + 2 → x = 1
        have hx1_eq : x = 1 := by linarith
        constructor; linarith; linarith
