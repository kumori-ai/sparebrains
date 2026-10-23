import Mathlib

open scoped Nat
open scoped Real

/--
Find $9^{-1} \pmod{100}$, as a residue modulo 100.  (Give an answer between 0 and 99, inclusive.) -/
theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by
  have h₂ : x * 9 % 100 = 1 := h₁
  have h₃ : x * 9 ≥ 1 := by
    omega
  have h₄ : x * 9 < 900 := by
    omega
  have h₅ : ∃ k : ℕ, x * 9 = 1 + 100 * k := by
    use (x * 9 - 1) / 100
    have h₅₁ : 100 * ((x * 9 - 1) / 100) ≤ x * 9 - 1 := Nat.mul_div_le (x * 9 - 1) 100
    have h₅₂ : x * 9 - 1 < 100 * ((x * 9 - 1) / 100 + 1) := by
      omega
    have h₅₃ : x * 9 - 1 - 100 * ((x * 9 - 1) / 100) < 100 := by
      omega
    have h₅₄ : x * 9 % 100 = x * 9 - 100 * ((x * 9 - 1) / 100) + (1 - 1) := by
      omega
    omega
  -- Simpler approach: just check all possibilities
  have h₆ : x = 89 := by
    interval_cases x <;> simp_all
    <;> omega
  exact h₆
