import Mathlib

open scoped Nat
open scoped Real

/--
The least common multiple of two numbers is 3720, and their greatest common divisor is 8. Given that one of the numbers is 120, what is the other number? -/
theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  have hprod : 8 * 3720 = 120 * b := by
    calc
      8 * 3720 = (Nat.gcd 120 b) * (Nat.lcm 120 b) := by rw [h₁, h₀]
      _ = 120 * b := by rw [Nat.gcd_mul_lcm]
  omega
