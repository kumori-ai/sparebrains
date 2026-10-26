import Mathlib

open scoped Nat
open scoped Real

/--
If $A$, $B$, and $C$ represent three distinct digits from 1 to 9 and they satisfy the following equations, what is the value of the sum $A+B+C$? (In the equation below, $AA$ represents a two-digit number both of whose digits are $A$.) $$A+B=C$$$$AA-B=2\times C$$$$C\times B=AA+A$$ -/
theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_all : ∀ a : ℕ, 1 ≤ a → a ≤ 9 → ∀ b : ℕ, 1 ≤ b → b ≤ 9 → ∀ c : ℕ, 1 ≤ c → c ≤ 9 →
    a ≠ b → a ≠ c → b ≠ c → a + b = c → 10 * a + a - b = 2 * c → c * b = 10 * a + a + a → a + b + c = 8 := by
    decide
  exact h_all a h₀.1 h₀.2 b h₁.1 h₁.2 c h₂.1 h₂.2 h₃ h₄ h₅ h₆ h₇ h₈
