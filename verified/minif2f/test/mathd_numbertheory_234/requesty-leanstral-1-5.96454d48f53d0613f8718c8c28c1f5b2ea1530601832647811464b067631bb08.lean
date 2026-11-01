import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  rcases h₀ with ⟨ha1, ha2, hb⟩
  have h_all : ∀ (a' : ℕ), 1 ≤ a' → a' ≤ 9 → ∀ (b' : ℕ), b' ≤ 9 → ((10 * a' + b') ^ 3 = 912673 → a' + b' = 16) := by
    decide
  exact h_all a ha1 ha2 b hb h₁
