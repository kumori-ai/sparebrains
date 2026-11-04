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
  have hp_mem : p ∈ ({5,7,11,13,17} : Finset ℕ) := by
    have h_primes_eq : (Finset.Icc 4 18).filter Nat.Prime = {5,7,11,13,17} := by decide
    have hp_mem_Icc : p ∈ Finset.Icc 4 18 := Finset.mem_Icc.mpr ⟨hp4, hp18⟩
    have hp_mem_filter : p ∈ (Finset.Icc 4 18).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨hp_mem_Icc, hp⟩
    rw [h_primes_eq] at hp_mem_filter
    exact hp_mem_filter
  have hq_mem : q ∈ ({5,7,11,13,17} : Finset ℕ) := by
    have h_primes_eq : (Finset.Icc 4 18).filter Nat.Prime = {5,7,11,13,17} := by decide
    have hq_mem_Icc : q ∈ Finset.Icc 4 18 := Finset.mem_Icc.mpr ⟨hq4, hq18⟩
    have hq_mem_filter : q ∈ (Finset.Icc 4 18).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨hq_mem_Icc, hq⟩
    rw [h_primes_eq] at hq_mem_filter
    exact hq_mem_filter
  have h_all : ∀ a ∈ ({5,7,11,13,17} : Finset ℕ), ∀ b ∈ ({5,7,11,13,17} : Finset ℕ), (a : ℤ) * (b : ℤ) - ((a : ℤ) + (b : ℤ)) ≠ (194 : ℤ) := by
    decide
  exact h_all p hp_mem q hq_mem
