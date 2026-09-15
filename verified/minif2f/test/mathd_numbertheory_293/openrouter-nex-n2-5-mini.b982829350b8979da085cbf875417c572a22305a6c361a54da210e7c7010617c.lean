import Mathlib

open scoped Nat
open scoped Real

/--
What digit must be placed in the blank to make the four-digit integer $20\_7$ a multiple of 11? -/
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  omega
