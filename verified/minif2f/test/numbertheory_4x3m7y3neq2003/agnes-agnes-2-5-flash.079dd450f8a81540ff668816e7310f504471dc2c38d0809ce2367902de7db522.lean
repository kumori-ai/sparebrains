import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (2003 : ℤ) % 7 := by rw [h]
  have : (4 * x ^ 3 - 7 * y ^ 3) % 7 = (4 * x ^ 3) % 7 := by
    have h1 : (7 * y ^ 3 : ℤ) % 7 = 0 := by simp [Int.mul_emod, Int.emod_emod]
    have h2 : ((4 * x ^ 3 - 7 * y ^ 3) % 7 : ℤ) = ((4 * x ^ 3) % 7 - (7 * y ^ 3) % 7) % 7 := by
      simp [Int.sub_emod]
    rw [h2, h1]
    have : (((4 * x ^ 3) % 7 : ℤ) - 0) % 7 = (4 * x ^ 3) % 7 := by
      simp [Int.sub_emod]
    simpa using this
  have : (2003 : ℤ) % 7 = 1 := by norm_num
  have h₃ : (x ^ 3 : ℤ) % 7 = 0 ∨ (x ^ 3 : ℤ) % 7 = 1 ∨ (x ^ 3 : ℤ) % 7 = 6 := by
    have : (x % 7 : ℤ) = 0 ∨ (x % 7 : ℤ) = 1 ∨ (x % 7 : ℤ) = 2 ∨ (x % 7 : ℤ) = 3 ∨ (x % 7 : ℤ) = 4 ∨ (x % 7 : ℤ) = 5 ∨ (x % 7 : ℤ) = 6 := by
      omega
    rcases this with (h | h | h | h | h | h | h) <;>
      (try { simp [h, pow_three, Int.mul_emod, Int.add_emod] }) <;>
      (try { omega }) <;>
      (try { simp [h, pow_three, Int.mul_emod, Int.add_emod] }) <;>
      (try { omega })
  rcases h₃ with (h₃ | h₃ | h₃) <;>
    simp [h₃, Int.mul_emod] at this ⊢ <;>
    omega
