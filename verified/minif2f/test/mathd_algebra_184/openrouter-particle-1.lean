import Mathlib

open scoped Nat
open scoped Real

/--
We have two geometric sequences of positive real numbers: $$6,a,b\text{ and }\frac{1}{b},a,54$$Solve for $a$. -/
theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 := by
  have h1R : (a : ℝ) ^ 2 = 6 * (b : ℝ) := by
    rw [← NNReal.coe_pow, h₁, NNReal.coe_mul]
    norm_num
  have h2R : (a : ℝ) ^ 2 = 54 / (b : ℝ) := by
    rw [← NNReal.coe_pow, h₂, NNReal.coe_div]
    norm_num
  have hbpos : (0 : ℝ) < (b : ℝ) := NNReal.coe_pos.mpr h₀.2
  have hb2 : (b : ℝ) ^ 2 = 9 := by
    have h : 6 * (b : ℝ) = 54 / (b : ℝ) := by linarith [h1R, h2R]
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    field_simp [hbne] at h
    nlinarith
  have hb3 : (b : ℝ) = 3 := by
    have h : ((b : ℝ) - 3) * ((b : ℝ) + 3) = 0 := by nlinarith [hb2]
    have hpos : (b : ℝ) + 3 ≠ 0 := by
      have : (0 : ℝ) < (b : ℝ) + 3 := by linarith
      exact ne_of_gt this
    have hzero : (b : ℝ) - 3 = 0 := (mul_eq_zero.mp h).resolve_right hpos
    linarith
  have ha2 : (a : ℝ) ^ 2 = 18 := by
    rw [h1R, hb3]
    norm_num
  have hapos : (0 : ℝ) < (a : ℝ) := NNReal.coe_pos.mpr h₀.1
  have haeq : (a : ℝ) = 3 * Real.sqrt 2 := by
    have hsq : (a : ℝ) ^ 2 = (3 * Real.sqrt 2) ^ 2 := by
      rw [ha2, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rcases h with h | h
    · exact h
    · have hpos : (0 : ℝ) < 3 * Real.sqrt 2 := by positivity
      nlinarith [hapos, hpos, h]
  apply NNReal.coe_injective
  rw [NNReal.coe_mul]
  norm_num
  change (a : ℝ) = 3 * Real.sqrt 2
  exact haeq
