import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have hsum : n + 4 + (n + 6) + (n + 8) = 3 * n + 18 := by ring
  rw [hsum]
  have h9 : 9 ∣ 3 * n + 18 := by
    have h3 : 3 ∣ n + 6 :=
      Nat.dvd_add h₁ (by norm_num : 3 ∣ 6)
    have h_eq : 3 * n + 18 = 3 * (n + 6) := by ring
    rw [h_eq]
    have h9_eq : 9 = 3 * 3 := by norm_num
    rw [h9_eq]
    exact Nat.mul_dvd_mul_left 3 h3
  exact Nat.mod_eq_zero_of_dvd h9
