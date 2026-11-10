import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $$\frac{\log_2 80}{\log_{40}2}-\frac{\log_2 160}{\log_{20}2}?$$

$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }\frac54 \qquad \textbf{(D) }2 \qquad \textbf{(E) }\log_2 5$ -/
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h80 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    rw [show (80 : ℝ) = 2 ^ 4 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    <;> ring
  have h40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    <;> ring
  have h160 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    rw [show (160 : ℝ) = 2 ^ 5 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    <;> ring
  have h20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    <;> ring
  rw [h80, h40, h160, h20]
  field_simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  ring
