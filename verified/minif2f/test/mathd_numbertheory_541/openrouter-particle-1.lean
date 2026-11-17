import Mathlib

open scoped Nat
open scoped Real

/--
The product of two positive whole numbers is 2005. If neither number is 1, what is the sum of the two numbers? -/
theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by
  by_cases hmn : m ≤ n
  · have hm_sq : m * m ≤ 2005 := by
      calc
        m * m ≤ m * n := Nat.mul_le_mul_left m hmn
        _ = 2005 := h₂
    have hm_le : m ≤ 44 := by
      by_contra h
      have h45 : 45 ≤ m := by omega
      have hsq : 45 * 45 ≤ m * m := Nat.mul_le_mul h45 h45
      norm_num at hsq
      omega
    have hm_ge : 2 ≤ m := by omega
    interval_cases m <;> omega
  · have hnm : n ≤ m := by omega
    have hn_sq : n * n ≤ 2005 := by
      calc
        n * n ≤ n * m := Nat.mul_le_mul_left n hnm
        _ = 2005 := by
          rw [mul_comm n m]
          exact h₂
    have hn_le : n ≤ 44 := by
      by_contra h
      have h45 : 45 ≤ n := by omega
      have hsq : 45 * 45 ≤ n * n := Nat.mul_le_mul h45 h45
      norm_num at hsq
      omega
    have hn_ge : 2 ≤ n := by omega
    interval_cases n <;> omega
