import Mathlib

open scoped Nat
open scoped Real

/--
The least common multiple of two numbers is 3720, and their greatest common divisor is 8. Given that one of the numbers is 120, what is the other number? -/
theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  have h₂ : 120 * b = 8 * 3720 := by
    rw [← Nat.gcd_mul_lcm 120 b]
    rw [h₁, h₀]
  have h₃ : 8 * 3720 = 120 * 248 := by norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 120) (by
    rw [h₂, h₃])
