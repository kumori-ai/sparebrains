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
  set A : ℝ := Real.log 3 / Real.log 2 with hAdef
  set B : ℝ := Real.log 2 / Real.log 3 with hBdef
  have hA : 0 < A := by
    rw [hAdef]
    exact div_pos h3 h2
  have hB : 0 < B := by
    rw [hBdef]
    exact div_pos h2 h3
  have hAB : A * B = 1 := by
    rw [hAdef, hBdef]
    field_simp [h2.ne', h3.ne'] <;> ring
  have hsqrtAB : Real.sqrt A * Real.sqrt B = 1 := by
    calc
      Real.sqrt A * Real.sqrt B = Real.sqrt (A * B) := (Real.sqrt_mul hA.le B).symm
      _ = Real.sqrt 1 := by rw [hAB]
      _ = 1 := Real.sqrt_one
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  have hsq : (Real.sqrt A + Real.sqrt B) ^ 2 =
      Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
    calc
      (Real.sqrt A + Real.sqrt B) ^ 2 = A + B + 2 := by
        rw [show (Real.sqrt A + Real.sqrt B) ^ 2 =
          (Real.sqrt A) ^ 2 + (Real.sqrt B) ^ 2 + 2 * (Real.sqrt A * Real.sqrt B) by ring]
        rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, hsqrtAB]
        ring
      _ = Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 := by
        rw [hlog6]
        rw [hAdef, hBdef]
        field_simp [h2.ne', h3.ne'] <;> ring
  calc
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3)
        = Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by rw [← hsq]
    _ = |Real.sqrt A + Real.sqrt B| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt A + Real.sqrt B :=
      abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
