import Mathlib

open scoped Nat
open scoped Real

/--
Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.

Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have hx : 0 ≤ (x : ℝ) := by positivity
  change Real.sqrt ((60 : ℝ) * (x : ℝ)) * Real.sqrt ((12 : ℝ) * (x : ℝ)) *
      Real.sqrt ((63 : ℝ) * (x : ℝ)) =
    (36 : ℝ) * (x : ℝ) * Real.sqrt ((35 : ℝ) * (x : ℝ))
  have h60 : 0 ≤ (60 : ℝ) := by norm_num
  have h12 : 0 ≤ (12 : ℝ) := by norm_num
  have h63 : 0 ≤ (63 : ℝ) := by norm_num
  have h35 : 0 ≤ (35 : ℝ) := by norm_num
  rw [Real.sqrt_mul h60, Real.sqrt_mul h12, Real.sqrt_mul h63, Real.sqrt_mul h35]
  have hconst : Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ) * Real.sqrt (63 : ℝ) =
      36 * Real.sqrt (35 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 60)]
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (60 : ℝ) * 12)]
    have hnum : (60 : ℝ) * 12 * 63 = (36 : ℝ) ^ 2 * 35 := by norm_num
    rw [hnum]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (36 : ℝ) ^ 2)]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 36)]
  have hx_sq : (Real.sqrt (x : ℝ)) ^ 2 = (x : ℝ) := Real.sq_sqrt hx
  calc
    (Real.sqrt (60 : ℝ) * Real.sqrt (x : ℝ)) *
        (Real.sqrt (12 : ℝ) * Real.sqrt (x : ℝ)) *
        (Real.sqrt (63 : ℝ) * Real.sqrt (x : ℝ))
        = (Real.sqrt (60 : ℝ) * Real.sqrt (12 : ℝ) * Real.sqrt (63 : ℝ)) *
            (Real.sqrt (x : ℝ)) ^ 3 := by ring
    _ = (36 * Real.sqrt (35 : ℝ)) * (Real.sqrt (x : ℝ)) ^ 3 := by rw [hconst]
    _ = (36 : ℝ) * (x : ℝ) * (Real.sqrt (35 : ℝ) * Real.sqrt (x : ℝ)) := by
      rw [show (Real.sqrt (x : ℝ)) ^ 3 =
          (Real.sqrt (x : ℝ)) ^ 2 * Real.sqrt (x : ℝ) by ring]
      rw [hx_sq]
      ring
