import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have h₂ : 4 * (m : ℝ) = 3 * (a : ℝ) := by
    have h₃ : (a : ℝ) ≠ 0 := by exact_mod_cast h₀.2.ne'
    field_simp [h₃] at h₁
    linarith
  have h₃ : (m : ℝ) + (a : ℝ) ≠ 0 := by
    have : 0 < (m : ℝ) + (a : ℝ) := by exact_mod_cast add_pos h₀.1 h₀.2
    exact ne_of_gt this
  have h₄ : 84 * (m : ℝ) + 70 * (a : ℝ) = 76 * ((m : ℝ) + (a : ℝ)) := by
    linarith [h₂]
  rw [h₄]
  field_simp [h₃]
