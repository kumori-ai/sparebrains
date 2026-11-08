import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have hm : m = n + 2 := by omega
  subst hm
  have hn : n ≤ 16 := by
    by_contra h
    push_neg at h
    have hle : 19 * 17 ≤ (n + 2) * n := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hn2 : 16 ≤ n := by
    by_contra h
    push_neg at h
    have hle : (n + 2) * n ≤ 17 * 15 := Nat.mul_le_mul (by omega) (by omega)
    omega
  omega
