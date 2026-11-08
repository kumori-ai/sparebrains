import Mathlib

open scoped Nat
open scoped Real

/--
Calculate $\sqrt{60x} \cdot \sqrt{12x} \cdot \sqrt{63x}$ . Express your answer in simplest radical form in terms of $x$.

Note: When entering a square root with more than one character, you must use parentheses or brackets.  For example, you should enter $\sqrt{14}$ as "sqrt(14)" or "sqrt{14}". -/
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have ha : (0 : ℝ) ≤ (x : ℝ) := by positivity
  push_cast
  calc Real.sqrt (60 * (x : ℝ)) * Real.sqrt (12 * (x : ℝ)) * Real.sqrt (63 * (x : ℝ))
      = Real.sqrt ((60 * (x : ℝ)) * (12 * (x : ℝ)) * (63 * (x : ℝ))) := by
        rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 60 * (x : ℝ)),
            ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (60 * (x : ℝ)) * (12 * (x : ℝ)))]
    _ = Real.sqrt (45360 * (x : ℝ) ^ 3) := by
        congr 1
        ring
    _ = Real.sqrt ((36 * (x : ℝ)) ^ 2 * (35 * (x : ℝ))) := by
        congr 1
        ring
    _ = Real.sqrt ((36 * (x : ℝ)) ^ 2) * Real.sqrt (35 * (x : ℝ)) :=
        Real.sqrt_mul (by positivity) _
    _ = 36 * (x : ℝ) * Real.sqrt (35 * (x : ℝ)) := by
        rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 36 * (x : ℝ))]
