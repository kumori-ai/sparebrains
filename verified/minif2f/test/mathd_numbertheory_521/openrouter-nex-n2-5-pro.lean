import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h₄ : m = n + 2 := by omega
  rw [h₄] at h₃
  have h₅ : n ≤ 16 := by
    by_contra h
    have h₆ : 17 ≤ n := by omega
    have h₇ : 19 ≤ n + 2 := by omega
    have h₈ : 19 * 17 ≤ (n + 2) * n := by
      calc
        19 * 17 ≤ (n + 2) * 17 := Nat.mul_le_mul_right 17 h₇
        _ ≤ (n + 2) * n := Nat.mul_le_mul_left (n + 2) h₆
    omega
  have h₆ : 16 ≤ n := by
    by_contra h
    have h₇ : n ≤ 15 := by omega
    have h₈ : n + 2 ≤ 17 := by omega
    have h₉ : (n + 2) * n ≤ 17 * 15 := by
      calc
        (n + 2) * n ≤ (n + 2) * 15 := Nat.mul_le_mul_left (n + 2) h₇
        _ ≤ 17 * 15 := Nat.mul_le_mul_right 15 h₈
    omega
  omega
