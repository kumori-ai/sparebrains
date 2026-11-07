import Mathlib

open scoped Nat
open scoped Real

/-- Which of the following is the value of $\sqrt{\log_2{6}+\log_3{6}}?$

$\textbf{(A) } 1 \qquad\textbf{(B) } \sqrt{\log_5{6}} \qquad\textbf{(C) } 2 \qquad\textbf{(D) } \sqrt{\log_2{3}}+\sqrt{\log_3{2}} \qquad\textbf{(E) } \sqrt{\log_2{6}}+\sqrt{\log_3{6}}$ -/
theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h2ne : Real.log 2 ≠ 0 := ne_of_gt h2
  have h3ne : Real.log 3 ≠ 0 := ne_of_gt h3
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    have h : (6 : ℝ) = 2 * 3 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have hx : 0 < Real.log 3 / Real.log 2 := div_pos h3 h2
  have hy : 0 < Real.log 2 / Real.log 3 := div_pos h2 h3
  have hxy : (Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3) = 1 := by
    rw [div_mul_div_comm, mul_comm (Real.log 3) (Real.log 2),
      div_self (mul_ne_zero h2ne h3ne)]
  have hmid : Real.sqrt (Real.log 3 / Real.log 2) *
      Real.sqrt (Real.log 2 / Real.log 3) = 1 := by
    rw [← Real.sqrt_mul hx.le, hxy, Real.sqrt_one]
  have hmid2 : 2 * Real.sqrt (Real.log 3 / Real.log 2) *
      Real.sqrt (Real.log 2 / Real.log 3) = 2 := by
    calc 2 * Real.sqrt (Real.log 3 / Real.log 2) *
          Real.sqrt (Real.log 2 / Real.log 3)
        = 2 * (Real.sqrt (Real.log 3 / Real.log 2) *
            Real.sqrt (Real.log 2 / Real.log 3)) := by ring
      _ = 2 := by rw [hmid]; norm_num
  have hsq : (Real.sqrt (Real.log 3 / Real.log 2) +
        Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 =
      Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
    rw [add_sq, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, hmid2]
    ring
  have harg : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 =
      (Real.sqrt (Real.log 3 / Real.log 2) +
        Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
    calc Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3
        = (Real.log 2 + Real.log 3) / Real.log 2 +
            (Real.log 2 + Real.log 3) / Real.log 3 := by rw [h6]
      _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
          rw [add_div, add_div, div_self h2ne, div_self h3ne]
          ring
      _ = (Real.sqrt (Real.log 3 / Real.log 2) +
            Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by rw [hsq]
  rw [harg, Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
