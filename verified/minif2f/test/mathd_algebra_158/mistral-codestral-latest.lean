import Mathlib

open scoped Nat
open scoped Real

/--
The sum of 5 consecutive even integers is 4 less than the sum of the first 8 consecutive odd counting numbers. What is the smallest of the even integers? -/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k ∈ Finset.range 8, (2 * k + 1)) - ↑(∑ k ∈ Finset.range 5, (a + 2 * k)) = (4 : ℤ)) :
    a = 8 := by
  have h₂ : ∑ k ∈ Finset.range 8, (2 * k + 1) = 64 := by
    simp only [Finset.sum_range_succ, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_id,
      add_assoc, add_comm, add_left_comm, mul_add, mul_comm, mul_assoc]
    ring_nf
  have h₃ : ∑ k ∈ Finset.range 5, (a + 2 * k) = 5 * a + 20 := by
    simp only [Finset.sum_range_succ, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_id,
      add_assoc, add_comm, add_left_comm, mul_add, mul_comm, mul_assoc]
    ring_nf
  rw [h₂, h₃] at h₁
  simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_id, add_assoc, add_comm,
    add_left_comm, mul_add, mul_comm, mul_assoc] at h₁
  ring_nf at h₁
  linarith
