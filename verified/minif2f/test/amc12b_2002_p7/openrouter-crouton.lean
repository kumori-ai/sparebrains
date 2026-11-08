import Mathlib

open scoped Nat
open scoped Real

/--
The product of three consecutive positive integers is $ 8$ times their sum. What is the sum of their squares?

$ \textbf{(A)}\ 50 \qquad
\textbf{(B)}\ 77 \qquad
\textbf{(C)}\ 110 \qquad
\textbf{(D)}\ 149 \qquad
\textbf{(E)}\ 194$ -/
theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
  obtain ⟨ha, hb, hc⟩ := h₀
  subst h₁
  subst h₂
  have key : (a * (a + 2)) * (a + 1) = 24 * (a + 1) := by
    calc (a * (a + 2)) * (a + 1) = a * (a + 1) * (a + 1 + 1) := by ring
      _ = 8 * (a + (a + 1) + (a + 1 + 1)) := h₃
      _ = 24 * (a + 1) := by ring
  have h_eq : a * (a + 2) = 24 := mul_right_cancel₀ (by omega : a + 1 ≠ 0) key
  have ha_le : a ≤ 24 := by
    have hle : a ≤ a * (a + 2) := by
      calc a = a * 1 := by ring
        _ ≤ a * (a + 2) := Nat.mul_le_mul_left a (by omega)
    omega
  interval_cases a <;> norm_num at h_eq <;> norm_num
