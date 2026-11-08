import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have ha : (0 : ℝ) < a := by exact_mod_cast h₀.2
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha
  have h_eq : (m : ℝ) = 3 / 4 * (a : ℝ) := by
    rw [div_eq_iff ha_ne] at h₁
    exact h₁
  have hsum_ne : (3 / 4 * (a : ℝ) + (a : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < 3 / 4 * (a : ℝ) + (a : ℝ) := by linarith
    exact ne_of_gt hpos
  rw [h_eq, div_eq_iff hsum_ne]
  ring
