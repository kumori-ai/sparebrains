import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $$\frac{\log_2 80}{\log_{40}2}-\frac{\log_2 160}{\log_{20}2}?$$

$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }\frac54 \qquad \textbf{(D) }2 \qquad \textbf{(E) }\log_2 5$ -/
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h80 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    have h : (80 : ℝ) = 2 ^ 4 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    have h : (40 : ℝ) = 2 ^ 3 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h160 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    have h : (160 : ℝ) = 2 ^ 5 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    have h : (20 : ℝ) = 2 ^ 2 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [h80, h40, h160, h20]
  have ha' : Real.log 2 ≠ 0 := ne_of_gt ha
  have h40' : 3 * Real.log 2 + Real.log 5 ≠ 0 := ne_of_gt (by linarith)
  have h20' : 2 * Real.log 2 + Real.log 5 ≠ 0 := ne_of_gt (by linarith)
  field_simp [ha', h40', h20']
  ring
