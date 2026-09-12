import Mathlib

open scoped Nat
open scoped Real

/--
When a number is divided by 5, the remainder is 3. What is the remainder when twice the number is divided by 5? -/
theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by
  have h1 : 2 * n % 5 = ((2 % 5) * (n % 5)) % 5 := by
    simpa using Nat.mul_mod 2 n 5
  have h2 : 2 * n % 5 = ((2 % 5) * 3) % 5 := by
    simpa [h₀] using h1
  have h3 : 2 * n % 5 = (2 * 3) % 5 := by
    simpa using h2
  simpa using h3
