import Mathlib

open scoped Nat
open scoped Real

/-- What is the value of $$\frac{\log_2 80}{\log_{40}2}-\frac{\log_2 160}{\log_{20}2}?$$

$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }\frac54 \qquad \textbf{(D) }2 \qquad \textbf{(E) }\log_2 5$ -/
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h40 : Real.log 40 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h20 : Real.log 20 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hdiv1 : Real.log 2 / Real.log 40 ≠ 0 := div_ne_zero h2 h40
  have hdiv2 : Real.log 2 / Real.log 20 ≠ 0 := div_ne_zero h2 h20
  have e80 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    have h : (80 : ℝ) = 2 ^ 4 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have e40 : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    have h : (40 : ℝ) = 2 ^ 3 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have e160 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    have h : (160 : ℝ) = 2 ^ 5 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have e20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    have h : (20 : ℝ) = 2 ^ 2 * 5 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have key : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      (Real.log 80 * Real.log 40 - Real.log 160 * Real.log 20) / (Real.log 2) ^ 2 := by
    field_simp
  rw [key, e80, e40, e160, e20]
  have hnum : (4 * Real.log 2 + Real.log 5) * (3 * Real.log 2 + Real.log 5) -
      (5 * Real.log 2 + Real.log 5) * (2 * Real.log 2 + Real.log 5) =
        2 * (Real.log 2) ^ 2 := by ring
  have hsq : (Real.log 2) ^ 2 ≠ 0 := pow_ne_zero 2 h2
  rw [hnum, mul_div_assoc, div_self hsq, mul_one]
