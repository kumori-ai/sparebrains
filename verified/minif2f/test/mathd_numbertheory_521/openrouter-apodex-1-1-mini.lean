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
    have : n ≥ 17 := by omega
    have : (n + 2) * n > 288 := by
      have : n + 2 ≥ 19 := by omega
      nlinarith
    omega
  have h₆ : n ≥ 16 := by
    by_contra h
    have : n ≤ 15 := by omega
    have : (n + 2) * n < 288 := by
      have : n + 2 ≤ 17 := by omega
      nlinarith
    omega
  have h₇ : n = 16 := by omega
  rw [h₇] at h₄
  omega
