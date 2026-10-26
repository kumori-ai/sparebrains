import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  rcases h₀ with ⟨hm, ha⟩
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ha)
  have h_sum_pos : 0 < (m : ℝ) + (a : ℝ) := add_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr ha)
  have h_sum_ne_zero : (m : ℝ) + (a : ℝ) ≠ 0 := h_sum_pos.ne.symm
  field_simp [ha'] at h₁
  -- h₁ : (m : ℝ) * 4 = (a : ℝ) * 3
  field_simp [h_sum_ne_zero]
  nlinarith
