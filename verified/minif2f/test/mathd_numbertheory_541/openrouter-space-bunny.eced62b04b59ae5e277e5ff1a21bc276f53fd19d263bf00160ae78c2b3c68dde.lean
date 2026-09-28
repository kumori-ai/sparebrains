import Mathlib

open scoped Nat
open scoped Real

/--
The product of two positive whole numbers is 2005. If neither number is 1, what is the sum of the two numbers? -/
theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by
  rcases Nat.le_total m n with hmn | hnm
  · have hm_sq : m * m ≤ m * n := Nat.mul_le_mul_left m hmn
    have hm : m ≤ 44 := by nlinarith [hm_sq, h₂]
    interval_cases m <;> omega
  · have hn_sq : n * n ≤ n * m := Nat.mul_le_mul_left n hnm
    have hn : n ≤ 44 := by nlinarith [hn_sq, h₂]
    interval_cases n <;> omega
