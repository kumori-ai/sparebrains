import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  rcases h₀ with ⟨ha1, ha9, hb9⟩
  interval_cases a <;> interval_cases b <;> norm_num at h₁ <;> omega
