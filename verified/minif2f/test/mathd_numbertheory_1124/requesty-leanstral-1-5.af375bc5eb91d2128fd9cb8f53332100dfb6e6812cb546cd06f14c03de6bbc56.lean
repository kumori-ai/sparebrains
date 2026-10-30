import Mathlib

open scoped Nat
open scoped Real

/-- The four-digit number $\underline{374n}$ is divisible by 18. Find the units digit $n$. -/
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
  have h_all : ∀ n : ℕ, n ≤ 9 → (18 ∣ 374 * 10 + n → n = 4) := by
    decide
  exact h_all n h₀ h₁
