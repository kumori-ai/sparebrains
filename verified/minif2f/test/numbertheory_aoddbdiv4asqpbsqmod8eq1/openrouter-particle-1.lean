import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  rcases h₀ with ⟨k, rfl⟩
  rcases h₁ with ⟨m, rfl⟩
  push_cast
  have hk : Even (k * (k + 1)) := Int.even_mul_succ_self k
  rcases hk with ⟨t, ht⟩
  have h_expand : (2 * k + 1) ^ 2 + (4 * (m : ℤ)) ^ 2 = 8 * t + 1 + 16 * (m : ℤ) ^ 2 := by
    rw [show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring]
    rw [ht]
    ring
  rw [h_expand]
  have hq : 8 * t + 1 + 16 * (m : ℤ) ^ 2 = 1 + (t + 2 * (m : ℤ) ^ 2) * 8 := by ring
  rw [hq]
  rw [show (t + 2 * (m : ℤ) ^ 2) * 8 = 8 * (t + 2 * (m : ℤ) ^ 2) by ring]
  rw [Int.add_mul_emod_self_left]
  norm_num
