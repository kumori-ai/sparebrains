import Mathlib

open scoped Nat
open scoped Real

/--
Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class’s mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A) }74 \qquad \textbf{(B) }75 \qquad \textbf{(C) }76 \qquad \textbf{(D) }77 \qquad \textbf{(E) }78$ -/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have h₂ : (4 : ℝ) * ↑m = 3 * ↑a := by
    have h₂₁ : (↑m : ℝ) / ↑a = 3 / 4 := h₁
    field_simp [h₀.2.ne'] at h₂₁
    ring_nf at h₂₁ ⊢
    norm_cast at h₂₁ ⊢
    <;> linarith
  have h₃ : (↑m + ↑a : ℝ) ≠ 0 := by
    have h₃₁ : (0 : ℝ) < ↑m := by exact_mod_cast h₀.1
    have h₃₂ : (0 : ℝ) < ↑a := by exact_mod_cast h₀.2
    linarith
  rw [div_eq_mul_inv]
  rw [mul_comm]
  have h₄ : (84 * ↑m + 70 * ↑a : ℝ) * 4 = (76 : ℝ) * (4 * ↑m + 4 * ↑a) := by
    rw [h₂]
    ring_nf
    <;> norm_num
    <;> linarith
  have h₅ : (4 : ℝ) ≠ 0 := by norm_num
  field_simp [h₃, h₅]
  linarith
