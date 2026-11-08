import Mathlib

open scoped Nat
open scoped Real

/-- Which of the following is the value of $\sqrt{\log_2{6}+\log_3{6}}?$

$\textbf{(A) } 1 \qquad\textbf{(B) } \sqrt{\log_5{6}} \qquad\textbf{(C) } 2 \qquad\textbf{(D) } \sqrt{\log_2{3}}+\sqrt{\log_3{2}} \qquad\textbf{(E) } \sqrt{\log_2{6}}+\sqrt{\log_3{6}}$ -/
theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    have h : (6 : ℝ) = 2 * 3 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have hx : 0 ≤ Real.log 3 / Real.log 2 := le_of_lt (div_pos hb ha)
  have hy : 0 ≤ Real.log 2 / Real.log 3 := le_of_lt (div_pos ha hb)
  have hprod : Real.log 3 / Real.log 2 * (Real.log 2 / Real.log 3) = 1 := by
    field_simp
  have hsum : Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 =
      Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
    rw [h6]
    field_simp
    ring
  have hsq : (Real.sqrt (Real.log 3 / Real.log 2) +
      Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 =
      Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
    have h1 : (Real.sqrt (Real.log 3 / Real.log 2) +
        Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 =
        (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 +
        (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 +
        2 * (Real.sqrt (Real.log 3 / Real.log 2) *
          Real.sqrt (Real.log 2 / Real.log 3)) := by ring
    rw [h1, Real.sq_sqrt hx, Real.sq_sqrt hy]
    have h2 : Real.sqrt (Real.log 3 / Real.log 2) *
        Real.sqrt (Real.log 2 / Real.log 3) = 1 := by
      rw [← Real.sqrt_mul hx, hprod, Real.sqrt_one]
    rw [h2]
    linarith
  have hnonneg : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) +
      Real.sqrt (Real.log 2 / Real.log 3) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3)
      = Real.sqrt ((Real.sqrt (Real.log 3 / Real.log 2) +
          Real.sqrt (Real.log 2 / Real.log 3)) ^ 2) := by rw [hsq]
    _ = Real.sqrt (Real.log 3 / Real.log 2) +
          Real.sqrt (Real.log 2 / Real.log 3) := Real.sqrt_sq hnonneg
