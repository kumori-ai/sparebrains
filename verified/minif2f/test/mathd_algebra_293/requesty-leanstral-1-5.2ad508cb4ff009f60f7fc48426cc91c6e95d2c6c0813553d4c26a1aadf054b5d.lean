import Mathlib

open scoped Nat
open scoped Real

/--
Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.

Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have hx : 0 ≤ (x : ℝ) := x.2
  have h60x : 0 ≤ (60 : ℝ) * (x : ℝ) := by nlinarith
  have h60_12x : 0 ≤ ((60 : ℝ) * (x : ℝ)) * ((12 : ℝ) * (x : ℝ)) := by nlinarith
  have h36x : 0 ≤ (36 : ℝ) * (x : ℝ) := by nlinarith
  have h36x_sq : 0 ≤ ((36 : ℝ) * (x : ℝ)) ^ 2 := sq_nonneg _
  calc
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x)
        = (Real.sqrt (60 * x) * Real.sqrt (12 * x)) * Real.sqrt (63 * x) := by ring
    _ = Real.sqrt ((60 * x) * (12 * x)) * Real.sqrt (63 * x) := by
      rw [← Real.sqrt_mul h60x]
    _ = Real.sqrt (((60 * x) * (12 * x)) * (63 * x)) := by
      rw [← Real.sqrt_mul h60_12x]
    _ = Real.sqrt (45360 * (x : ℝ)^3) := by ring
    _ = Real.sqrt (((36 : ℝ) * (x : ℝ))^2 * (35 * (x : ℝ))) := by
      rw [show (45360 : ℝ) * (x : ℝ)^3 = ((36 : ℝ) * (x : ℝ))^2 * (35 * (x : ℝ)) by ring]
    _ = Real.sqrt (((36 : ℝ) * (x : ℝ))^2) * Real.sqrt (35 * (x : ℝ)) := by
      rw [Real.sqrt_mul h36x_sq]
    _ = ((36 : ℝ) * (x : ℝ)) * Real.sqrt (35 * (x : ℝ)) := by
      rw [Real.sqrt_sq h36x]
    _ = 36 * x * Real.sqrt (35 * x) := by ring
