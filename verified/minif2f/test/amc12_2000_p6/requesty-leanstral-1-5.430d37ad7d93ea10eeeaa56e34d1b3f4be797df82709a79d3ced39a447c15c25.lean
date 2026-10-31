import Mathlib

open scoped Nat
open scoped Real

/--
Two different prime numbers between $ 4$ and $ 18$ are chosen. When their sum is subtracted from their product, which of the following numbers could be obtained?

$ \textbf{(A)}\  21 \qquad \textbf{(B)}\  60\qquad \textbf{(C)}\ 119 \qquad \textbf{(D)}\  180\qquad \textbf{(E)}\ 231$ -/
theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q : ℤ) ≠ (194 : ℤ) := by
  rcases h₀ with ⟨hp, hq⟩
  rcases h₁ with ⟨hp4, hp18⟩
  rcases h₂ with ⟨hq4, hq18⟩
  have h_all : ∀ p ∈ Finset.Icc 4 18, Nat.Prime p → ∀ q ∈ Finset.Icc 4 18, Nat.Prime q → (p : ℤ) * q - (p + q : ℤ) ≠ (194 : ℤ) := by
    decide
  exact h_all p (Finset.mem_Icc.mpr ⟨hp4, hp18⟩) hp q (Finset.mem_Icc.mpr ⟨hq4, hq18⟩) hq
