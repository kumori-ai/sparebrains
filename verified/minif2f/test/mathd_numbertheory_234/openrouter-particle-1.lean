import Mathlib

open scoped Nat
open scoped Real

/--
When the two-digit integer $``\text{AB}"$ is cubed, the value is $912,\!673$. What is $A + B$? -/
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
  set n := 10 * a + b with hn
  have hn_ge : 10 ≤ n := by
    rw [hn]
    omega
  have hn_le : n ≤ 99 := by
    rw [hn]
    omega
  have hcube : n ^ 3 = 912673 := by
    rw [hn]
    exact h₁
  interval_cases n <;> norm_num at hcube
  omega
