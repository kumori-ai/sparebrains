import Mathlib

open scoped Nat
open scoped Real

/--
Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.

Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  -- nonnegativity of `x`
  have hx : (0 : ℝ) ≤ (x : ℝ) := x.property
  -- nonnegativity of the factors
  have h60x : 0 ≤ (60 : ℝ) * (x : ℝ) := by
    have : (0 : ℝ) ≤ (60 : ℝ) := by norm_num
    exact mul_nonneg this hx
  have h12x : 0 ≤ (12 : ℝ) * (x : ℝ) := by
    have : (0 : ℝ) ≤ (12 : ℝ) := by norm_num
    exact mul_nonneg this hx
  have h63x : 0 ≤ (63 : ℝ) * (x : ℝ) := by
    have : (0 : ℝ) ≤ (63 : ℝ) := by norm_num
    exact mul_nonneg this hx
  -- combine the square roots
  calc
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x)
        = Real.sqrt ((60 * x) * (12 * x)) * Real.sqrt (63 * x) := by
          norm_num
    _ = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
      norm_num
    _ = Real.sqrt ((36 * x) ^ 2 * (35 * x)) := by
          have : ((60 : ℝ) * (x : ℝ)) * ((12 : ℝ) * (x : ℝ)) * ((63 : ℝ) * (x : ℝ)) =
                (36 * (x : ℝ)) ^ 2 * (35 * (x : ℝ)) := by
            ring
          simpa [pow_two] using congrArg Real.sqrt this
    _ = Real.sqrt ((36 * x) ^ 2) * Real.sqrt (35 * x) := by
      norm_num
    _ = (36 * x) * Real.sqrt (35 * x) := by
          have h36x : 0 ≤ (36 : ℝ) * (x : ℝ) := by
            have : (0 : ℝ) ≤ (36 : ℝ) := by norm_num
            exact mul_nonneg this hx
          have h_sqrt : Real.sqrt ((36 * x) ^ 2) = 36 * x := by
            simpa [pow_two] using Real.sqrt_mul_self h36x
          simpa [h_sqrt]
