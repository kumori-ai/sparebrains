import Mathlib

open scoped Nat
open scoped Real

/--
The Fibonacci sequence is the sequence 1, 1, 2, 3, 5, $\ldots$ where each term is the sum of the previous two terms. What is the remainder when the $100^{\mathrm{th}}$ term of the sequence is divided by 4? -/
theorem mathd_numbertheory_483 (a : ℕ → ℕ) (h₀ : a 1 = 1) (h₁ : a 2 = 1)
    (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) : a 100 % 4 = 3 := by
  have ha3 : a 3 = 2 := by
    have h : a 3 = a 2 + a 1 := h₂ 1
    rw [h₁, h₀] at h
    exact h
  have ha4 : a 4 = 3 := by
    have h : a 4 = a 3 + a 2 := h₂ 2
    rw [ha3, h₁] at h
    exact h
  have ha5 : a 5 = 5 := by
    have h : a 5 = a 4 + a 3 := h₂ 3
    rw [ha4, ha3] at h
    exact h
  have ha6 : a 6 = 8 := by
    have h : a 6 = a 5 + a 4 := h₂ 4
    rw [ha5, ha4] at h
    exact h
  have key : ∀ k : ℕ,
      a (6 * k + 1) % 4 = 1 ∧ a (6 * k + 2) % 4 = 1 ∧ a (6 * k + 3) % 4 = 2 ∧
      a (6 * k + 4) % 4 = 3 ∧ a (6 * k + 5) % 4 = 1 ∧ a (6 * k + 6) % 4 = 0 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show a 1 % 4 = 1
        rw [h₀]
      · show a 2 % 4 = 1
        rw [h₁]
      · show a 3 % 4 = 2
        rw [ha3]
      · show a 4 % 4 = 3
        rw [ha4]
      · show a 5 % 4 = 1
        rw [ha5]
      · show a 6 % 4 = 0
        rw [ha6]
    | succ k ih =>
      have c1 : a (6 * (k + 1) + 1) % 4 = 1 := by
        have h := h₂ (6 * k + 5)
        have e1 : (6 * k + 5) + 2 = 6 * (k + 1) + 1 := by ring
        have e2 : (6 * k + 5) + 1 = 6 * k + 6 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, ih.2.2.2.2.2, ih.2.2.2.2.1]
      have c2 : a (6 * (k + 1) + 2) % 4 = 1 := by
        have h := h₂ (6 * k + 6)
        have e1 : (6 * k + 6) + 2 = 6 * (k + 1) + 2 := by ring
        have e2 : (6 * k + 6) + 1 = 6 * (k + 1) + 1 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, c1, ih.2.2.2.2.2]
      have c3 : a (6 * (k + 1) + 3) % 4 = 2 := by
        have h := h₂ (6 * (k + 1) + 1)
        have e1 : (6 * (k + 1) + 1) + 2 = 6 * (k + 1) + 3 := by ring
        have e2 : (6 * (k + 1) + 1) + 1 = 6 * (k + 1) + 2 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, c2, c1]
      have c4 : a (6 * (k + 1) + 4) % 4 = 3 := by
        have h := h₂ (6 * (k + 1) + 2)
        have e1 : (6 * (k + 1) + 2) + 2 = 6 * (k + 1) + 4 := by ring
        have e2 : (6 * (k + 1) + 2) + 1 = 6 * (k + 1) + 3 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, c3, c2]
      have c5 : a (6 * (k + 1) + 5) % 4 = 1 := by
        have h := h₂ (6 * (k + 1) + 3)
        have e1 : (6 * (k + 1) + 3) + 2 = 6 * (k + 1) + 5 := by ring
        have e2 : (6 * (k + 1) + 3) + 1 = 6 * (k + 1) + 4 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, c4, c3]
      have c6 : a (6 * (k + 1) + 6) % 4 = 0 := by
        have h := h₂ (6 * (k + 1) + 4)
        have e1 : (6 * (k + 1) + 4) + 2 = 6 * (k + 1) + 6 := by ring
        have e2 : (6 * (k + 1) + 4) + 1 = 6 * (k + 1) + 5 := by ring
        rw [e1, e2] at h
        rw [h, Nat.add_mod, c5, c4]
      exact ⟨c1, c2, c3, c4, c5, c6⟩
  have h100 : a 100 % 4 = 3 := (key 16).2.2.2.1
  exact h100
