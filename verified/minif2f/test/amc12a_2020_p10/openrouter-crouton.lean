import Mathlib

open scoped Nat
open scoped Real

/--
There is a unique positive integer $n$ larger than 1 such that \[\log_2{(\log_{16}{n})} = \log_4{(\log_4{n})}.\]
What is the sum of the digits of $n?$

$\textbf{(A) } 4 \qquad \textbf{(B) } 7 \qquad \textbf{(C) } 8 \qquad \textbf{(D) } 11 \qquad \textbf{(E) } 13$ -/
theorem amc12a_2020_p10 (n : ℕ) (h₀ : 1 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
    (Nat.digits 10 n).sum = 13 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h₀
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have ht_pos : 0 < Real.logb 4 (n : ℝ) := Real.logb_pos (by norm_num) hn1
  have hlog2_ne : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog4_ne : Real.log 4 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
    have h : (16 : ℝ) = 4 ^ (2 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have h16 : Real.logb 16 (n : ℝ) = Real.logb 4 (n : ℝ) / 2 := by
    show Real.log (n : ℝ) / Real.log 16 = (Real.log (n : ℝ) / Real.log 4) / 2
    rw [hlog16, div_div, mul_comm (Real.log 4) 2]
  have h4 : Real.logb 4 (Real.logb 4 (n : ℝ))
      = Real.logb 2 (Real.logb 4 (n : ℝ)) / 2 := by
    show Real.log (Real.logb 4 (n : ℝ)) / Real.log 4
      = (Real.log (Real.logb 4 (n : ℝ)) / Real.log 2) / 2
    rw [hlog4, div_div, mul_comm (Real.log 2) 2]
  have hdiv : Real.logb 2 (Real.logb 4 (n : ℝ) / 2)
      = Real.logb 2 (Real.logb 4 (n : ℝ)) - 1 := by
    rw [Real.logb_div (ne_of_gt ht_pos) (by norm_num : (2 : ℝ) ≠ 0)]
    have h22 : Real.logb 2 (2 : ℝ) = 1 := by
      show Real.log 2 / Real.log 2 = 1
      exact div_self hlog2_ne
    rw [h22]
  rw [h16, hdiv, h4] at h₁
  have hlog2t : Real.logb 2 (Real.logb 4 (n : ℝ)) = 2 := by linarith
  have ht_eq : Real.logb 4 (n : ℝ) = 4 := by
    have h := Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) ht_pos
    rw [hlog2t] at h
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [h2] at h
    exact h.symm
  have hn_eq : (n : ℝ) = 256 := by
    have h := Real.rpow_logb (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (4 : ℝ) ≠ 1) hn0
    rw [ht_eq] at h
    have h4pow : (4 : ℝ) ^ (4 : ℝ) = 256 := by norm_num
    rw [h4pow] at h
    exact h.symm
  have hn_nat : n = 256 := by exact_mod_cast hn_eq
  subst hn_nat
  decide
