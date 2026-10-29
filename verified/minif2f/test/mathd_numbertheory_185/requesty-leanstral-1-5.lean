import Mathlib

open scoped Nat
open scoped Real

/--
When a number is divided by 5, the remainder is 3. What is the remainder when twice the number is divided by 5? -/
theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by
  calc
  2 * n % 5 = ((2 % 5) * (n % 5)) % 5 := by rw [Nat.mul_mod]
  _ = (2 * 3) % 5 := by rw [h₀, show (2 : ℕ) % 5 = 2 by norm_num]
  _ = 6 % 5 := by norm_num
  _ = 1 := by norm_num
