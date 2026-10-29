import Mathlib

open scoped Nat
open scoped Real

/--
Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.

Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have hx : 0 ≤ (x : ℝ) := x.2
  have hprod : Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ) * Real.sqrt (63 : ℝ) = 36 * Real.sqrt (35 : ℝ) := by
    calc
      Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ) * Real.sqrt (63 : ℝ)
          = (Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ)) * Real.sqrt (63 : ℝ) := by ring
      _ = Real.sqrt ((60 : ℝ) * 12) * Real.sqrt (63 : ℝ) := by
            rw [← Real.sqrt_mul (by norm_num : 0 ≤ (60 : ℝ)) 12]
      _ = Real.sqrt (((60 : ℝ) * 12) * 63) := by
            rw [← Real.sqrt_mul (by norm_num : 0 ≤ (60 * 12 : ℝ)) 63]
      _ = Real.sqrt (45360) := by norm_num
      _ = Real.sqrt (1296 * 35) := by norm_num
      _ = Real.sqrt ((36 : ℝ) ^ 2 * 35) := by norm_num
      _ = Real.sqrt ((36 : ℝ) ^ 2) * Real.sqrt 35 := by
            rw [Real.sqrt_mul (by norm_num : 0 ≤ (36 : ℝ) ^ 2) 35]
      _ = 36 * Real.sqrt 35 := by simp [Real.sqrt_sq (by norm_num : 0 ≤ (36 : ℝ))]
  calc
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x)
        = (Real.sqrt (60 : ℝ) * Real.sqrt x) * (Real.sqrt (12 : ℝ) * Real.sqrt x) * (Real.sqrt (63 : ℝ) * Real.sqrt x) := by
          simp [Real.sqrt_mul (by norm_num : 0 ≤ (60 : ℝ)) x,
                Real.sqrt_mul (by norm_num : 0 ≤ (12 : ℝ)) x,
                Real.sqrt_mul (by norm_num : 0 ≤ (63 : ℝ)) x]
    _ = (Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ) * Real.sqrt (63 : ℝ)) * ((Real.sqrt x) ^ 3) := by ring
    _ = (36 * Real.sqrt (35 : ℝ)) * ((Real.sqrt x) ^ 3) := by rw [hprod]
    _ = 36 * Real.sqrt (35 : ℝ) * ((Real.sqrt x) ^ 2 * Real.sqrt x) := by ring
    _ = 36 * Real.sqrt (35 : ℝ) * (x * Real.sqrt x) := by rw [Real.sq_sqrt hx]
    _ = 36 * x * Real.sqrt (35 : ℝ) * Real.sqrt x := by ring
    _ = 36 * x * (Real.sqrt (35 : ℝ) * Real.sqrt x) := by ring
    _ = 36 * x * Real.sqrt (35 * x) := by rw [← Real.sqrt_mul (by norm_num : 0 ≤ (35 : ℝ)) x]
