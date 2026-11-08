import Mathlib

open scoped Nat
open scoped Real

/--
The Fibonacci sequence is the sequence 1, 1, 2, 3, 5, $\ldots$ where each term is the sum of the previous two terms. What is the remainder when the $100^{\mathrm{th}}$ term of the sequence is divided by 4? -/
theorem mathd_numbertheory_483 (a : ℕ → ℕ) (h₀ : a 1 = 1) (h₁ : a 2 = 1)
    (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) : a 100 % 4 = 3 := by
  have h3 : a 3 = 2 := by
    have h := h₂ 1
    norm_num [h₀, h₁] at h
    exact h
  have h4 : a 4 = 3 := by
    have h := h₂ 2
    norm_num [h₁, h3] at h
    exact h
  have h5 : a 5 = 5 := by
    have h := h₂ 3
    norm_num [h3, h4] at h
    exact h
  have h6 : a 6 = 8 := by
    have h := h₂ 4
    norm_num [h4, h5] at h
    exact h
  have key : ∀ n : ℕ, a (6 * n + 1) % 4 = 1 ∧ a (6 * n + 2) % 4 = 1 ∧
      a (6 * n + 3) % 4 = 2 ∧ a (6 * n + 4) % 4 = 3 ∧
      a (6 * n + 5) % 4 = 1 ∧ a (6 * n + 6) % 4 = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        norm_num [h₀, h₁, h3, h4, h5, h6]
    | succ n ih =>
      obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ := ih
      have r7 : a (6 * n + 7) = a (6 * n + 6) + a (6 * n + 5) := by
        have h := h₂ (6 * n + 5)
        have e1 : 6 * n + 5 + 2 = 6 * n + 7 := by ring
        have e2 : 6 * n + 5 + 1 = 6 * n + 6 := by ring
        rw [e1, e2] at h
        exact h
      have r8 : a (6 * n + 8) = a (6 * n + 7) + a (6 * n + 6) := by
        have h := h₂ (6 * n + 6)
        have e1 : 6 * n + 6 + 2 = 6 * n + 8 := by ring
        have e2 : 6 * n + 6 + 1 = 6 * n + 7 := by ring
        rw [e1, e2] at h
        exact h
      have r9 : a (6 * n + 9) = a (6 * n + 8) + a (6 * n + 7) := by
        have h := h₂ (6 * n + 7)
        have e1 : 6 * n + 7 + 2 = 6 * n + 9 := by ring
        have e2 : 6 * n + 7 + 1 = 6 * n + 8 := by ring
        rw [e1, e2] at h
        exact h
      have r10 : a (6 * n + 10) = a (6 * n + 9) + a (6 * n + 8) := by
        have h := h₂ (6 * n + 8)
        have e1 : 6 * n + 8 + 2 = 6 * n + 10 := by ring
        have e2 : 6 * n + 8 + 1 = 6 * n + 9 := by ring
        rw [e1, e2] at h
        exact h
      have r11 : a (6 * n + 11) = a (6 * n + 10) + a (6 * n + 9) := by
        have h := h₂ (6 * n + 9)
        have e1 : 6 * n + 9 + 2 = 6 * n + 11 := by ring
        have e2 : 6 * n + 9 + 1 = 6 * n + 10 := by ring
        rw [e1, e2] at h
        exact h
      have r12 : a (6 * n + 12) = a (6 * n + 11) + a (6 * n + 10) := by
        have h := h₂ (6 * n + 10)
        have e1 : 6 * n + 10 + 2 = 6 * n + 12 := by ring
        have e2 : 6 * n + 10 + 1 = 6 * n + 11 := by ring
        rw [e1, e2] at h
        exact h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have e : 6 * (n + 1) + 1 = 6 * n + 7 := by ring
        rw [e, r7]
        omega
      · have e : 6 * (n + 1) + 2 = 6 * n + 8 := by ring
        rw [e, r8]
        omega
      · have e : 6 * (n + 1) + 3 = 6 * n + 9 := by ring
        rw [e, r9]
        omega
      · have e : 6 * (n + 1) + 4 = 6 * n + 10 := by ring
        rw [e, r10]
        omega
      · have e : 6 * (n + 1) + 5 = 6 * n + 11 := by ring
        rw [e, r11]
        omega
      · have e : 6 * (n + 1) + 6 = 6 * n + 12 := by ring
        rw [e, r12]
        omega
  have h := (key 16).2.2.2.1
  norm_num at h
  exact h
