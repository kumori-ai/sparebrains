import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have h1 : (4 * x ^ 3 - 7 * y ^ 3) % 7 = 2003 % 7 := by rw [h]
  have h2 : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (4 * (x % 7) ^ 3) % 7 := by
    simp [Int.mul_emod, Int.sub_emod, Int.pow_succ]
  have h3 : (2003 : ℤ) % 7 = 1 := by norm_num
  have h4 : (4 * (x % 7) ^ 3) % 7 = 1 := by
    rw [h2] at h1
    simpa [h3] using h1
  have h5 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
    have : x % 7 ≥ 0 := Int.emod_nonneg x (by norm_num)
    have : x % 7 < 7 := Int.emod_lt_of_pos x (by norm_num)
    omega
  rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5) <;>
    simp [h5, pow_three, Int.mul_emod, Int.sub_emod] at h4 <;>
    norm_num at h4 <;>
    contradiction
