import Mathlib

open scoped Nat
open scoped Real

/--
The product of two consecutive positive even integers is 288. What is the greater of the two integers? -/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h₄ : n ≤ m := by
    by_contra h
    rw [Nat.sub_eq_zero_of_le (by omega)] at h₂
    norm_num at h₂
  have h₅ : m = n + 2 := by
    rw [← Nat.add_sub_cancel' h₄]
    rw [h₂]
  rw [h₅] at h₃
  have h₆ : n = 16 := by
    have h₆₁ : n ≤ 16 := by
      by_contra h
      have h₆₂ : n ≥ 17 := by omega
      have h₆₃ : (n + 2) * n ≥ 19 * 17 := by
        calc
          (n + 2) * n ≥ 19 * n := by
            exact Nat.mul_le_mul_right n (by omega)
          _ ≥ 19 * 17 := by
            exact Nat.mul_le_mul_left 19 (by omega)
      omega
    have h₆₄ : n ≥ 16 := by
      by_contra h
      have h₆₅ : n ≤ 15 := by omega
      have h₆₆ : (n + 2) * n ≤ 17 * 15 := by
        calc
          (n + 2) * n ≤ 17 * n := by
            exact Nat.mul_le_mul_right n (by omega)
          _ ≤ 17 * 15 := by
            exact Nat.mul_le_mul_left 17 (by omega)
      omega
    omega
  rw [h₆] at h₅
  norm_num at h₅
  exact h₅
