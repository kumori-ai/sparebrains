import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h₄ : m = n + 2 := by
    have : n ≤ m := by omega
    omega
  rw [h₄] at h₃
  have h₅ : n * (n + 2) = 288 := by
    linarith
  have h₆ : n ≤ 16 := by
    by_contra h
    have h₆₁ : n ≥ 17 := by omega
    have h₆₂ : n * (n + 2) ≥ 17 * 19 := by
      calc
        n * (n + 2) ≥ 17 * (n + 2) := by nlinarith
        _ ≥ 17 * 19 := by nlinarith
    have h₆₃ : 17 * 19 > 288 := by norm_num
    linarith
  have h₇ : n ≥ 16 := by
    by_contra h
    have h₇₁ : n ≤ 15 := by omega
    have h₇₂ : n * (n + 2) ≤ 15 * 17 := by
      calc
        n * (n + 2) ≤ 15 * (n + 2) := by nlinarith
        _ ≤ 15 * 17 := by nlinarith
    have h₇₃ : 15 * 17 < 288 := by norm_num
    linarith
  have h₈ : n = 16 := by omega
  omega
