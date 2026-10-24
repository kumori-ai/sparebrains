import Mathlib

open scoped Nat
open scoped Real

/-- Which of the following is the value of $\sqrt{\log_2{6}+\log_3{6}}?$

$\textbf{(A) } 1 \qquad\textbf{(B) } \sqrt{\log_5{6}} \qquad\textbf{(C) } 2 \qquad\textbf{(D) } \sqrt{\log_2{3}}+\sqrt{\log_3{2}} \qquad\textbf{(E) } \sqrt{\log_2{6}}+\sqrt{\log_3{6}}$ -/
theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
  have h_pos_log2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_pos_log3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h_pos_log6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have h_nonzero2 : Real.log 2 ≠ 0 := by
    intro h
    rw [h] at h_pos_log2
    exact lt_irrefl 0 h_pos_log2
  have h_nonzero3 : Real.log 3 ≠ 0 := by
    intro h
    rw [h] at h_pos_log3
    exact lt_irrefl 0 h_pos_log3
  have h_nonzero6 : Real.log 6 ≠ 0 := by
    intro h
    rw [h] at h_pos_log6
    exact lt_irrefl 0 h_pos_log6
  have h₄ : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 =
      (Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2) := by
    calc
      Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 =
          Real.log (2 * 3) / Real.log 2 + Real.log (2 * 3) / Real.log 3 := by
        norm_num
      _ = (Real.log 2 + Real.log 3) / Real.log 2 + (Real.log 2 + Real.log 3) / Real.log 3 := by
        rw [Real.log_mul] <;> norm_num
      _ = 1 + Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 1 := by
        field_simp [h_nonzero2, h_nonzero3]
        <;> ring
      _ = Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 := by
        ring
  have h₅ : Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 =
      (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
    have h_a : 0 < Real.log 3 / Real.log 2 := by
      apply div_pos h_pos_log3 h_pos_log2
    have h_b : 0 < Real.log 2 / Real.log 3 := by
      apply div_pos h_pos_log2 h_pos_log3
    have h_sqrt_a_sq : Real.sqrt (Real.log 3 / Real.log 2) ^ 2 = Real.log 3 / Real.log 2 := by
      rw [Real.sq_sqrt] <;> linarith
    have h_sqrt_b_sq : Real.sqrt (Real.log 2 / Real.log 3) ^ 2 = Real.log 2 / Real.log 3 := by
      rw [Real.sq_sqrt] <;> linarith
    have h_cross : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) = 1 := by
      have h_val : Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3) =
          Real.sqrt ((Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3)) := by
        rw [Real.sqrt_mul] <;> linarith
      rw [h_val]
      have h_inner : (Real.log 3 / Real.log 2) * (Real.log 2 / Real.log 3) = 1 := by
        field_simp [h_nonzero2, h_nonzero3]
      rw [h_inner]
      norm_num
    calc
      Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 + 2 =
          (Real.sqrt (Real.log 3 / Real.log 2) ^ 2 +
            2 * (Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)) +
            Real.sqrt (Real.log 2 / Real.log 3) ^ 2) := by
        rw [h_sqrt_a_sq, h_sqrt_b_sq, h_cross]
        <;> ring
      _ = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := by
        ring
  have h₆ : 0 ≤ Real.log 3 / Real.log 2 + Real.log 2 / Real.log 3 := by
    positivity
  calc
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
        Real.sqrt ((Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2) := by
      rw [h₄]
      rw [h₅]
    _ = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
      rw [Real.sqrt_sq]
      apply le_of_lt
      apply add_pos
      · apply Real.sqrt_pos.mpr
        exact show 0 < Real.log 3 / Real.log 2 by positivity
      · apply Real.sqrt_pos.mpr
        exact show 0 < Real.log 2 / Real.log 3 by positivity
