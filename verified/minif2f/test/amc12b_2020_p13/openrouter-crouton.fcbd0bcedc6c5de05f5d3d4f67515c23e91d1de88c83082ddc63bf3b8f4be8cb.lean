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
  have hne2 : Real.log 2 ≠ 0 := ne_of_gt h2
  have hne3 : Real.log 3 ≠ 0 := ne_of_gt h3
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    have h : (6 : ℝ) = 2 * 3 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have hS_nonneg : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2
      = Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
    have h1 : (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 = Real.log 3 / Real.log 2 :=
      Real.sq_sqrt (div_nonneg (le_of_lt h3) (le_of_lt h2))
    have h2' : (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = Real.log 2 / Real.log 3 :=
      Real.sq_sqrt (div_nonneg (le_of_lt h2) (le_of_lt h3))
    have hprod : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) = 1 := by
      rw [← Real.sqrt_mul (div_nonneg (le_of_lt h3) (le_of_lt h2))]
      rw [div_mul_div_comm, mul_comm (Real.log 3) (Real.log 2),
        div_self (mul_ne_zero hne2 hne3), Real.sqrt_one]
    have hexp : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2
        = (Real.sqrt (Real.log 3 / Real.log 2)) ^ 2 + (Real.sqrt (Real.log 2 / Real.log 3)) ^ 2
          + 2 * (Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)) := by ring
    rw [hexp, h1, h2', hprod, h6, add_div, add_div, div_self hne2, div_self hne3]
    ring
  rw [← hsq, Real.sqrt_sq hS_nonneg]
