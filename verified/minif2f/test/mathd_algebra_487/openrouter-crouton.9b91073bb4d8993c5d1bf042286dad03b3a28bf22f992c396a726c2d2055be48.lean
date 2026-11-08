import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha : a ^ 2 + a = 1 := by
    rw [← h₀]
    linarith
  have hc : c ^ 2 + c = 1 := by
    rw [← h₂]
    linarith
  have hsum : a + c = -1 := by
    have hfactor : (a - c) * (a + c + 1) = 0 := by
      have hexp : (a - c) * (a + c + 1) = (a ^ 2 + a) - (c ^ 2 + c) := by ring
      rw [hexp, ha, hc]
      norm_num
    have hac : a - c ≠ 0 := sub_ne_zero.mpr h₄
    have hzero : a + c + 1 = 0 := by
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd h hac
      · exact h
    linarith
  have hsqsum : a ^ 2 + c ^ 2 = 3 := by linarith
  have hprod : a * c = -1 := by
    have hsq : (a + c) ^ 2 = 1 := by rw [hsum]; norm_num
    have hexp : (a + c) ^ 2 = a ^ 2 + c ^ 2 + 2 * (a * c) := by ring
    linarith
  have hdiff2 : (a - c) ^ 2 = 5 := by
    have hexp : (a - c) ^ 2 = a ^ 2 + c ^ 2 - 2 * (a * c) := by ring
    linarith
  have hbdiff : b - d = -(a - c) := by
    have hb : b = 1 - a := by linarith
    have hd : d = 1 - c := by linarith
    rw [hb, hd]
    ring
  have hbdiff2 : (b - d) ^ 2 = 5 := by
    rw [hbdiff]
    have hexp : (-(a - c)) ^ 2 = (a - c) ^ 2 := by ring
    rw [hexp, hdiff2]
  have htotal : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by linarith
  rw [htotal]
