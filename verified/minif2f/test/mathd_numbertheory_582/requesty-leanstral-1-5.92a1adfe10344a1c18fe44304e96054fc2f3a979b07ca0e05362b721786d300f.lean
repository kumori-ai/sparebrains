import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have h9 : 9 ∣ n + 4 + (n + 6) + (n + 8) := by
    have h_expr : n + 4 + (n + 6) + (n + 8) = 3*n + 18 := by ring
    rw [h_expr]
    have h9_3n : 9 ∣ 3*n := by
      simpa [show (3:ℕ)*3 = 9 by norm_num] using Nat.mul_dvd_mul_left 3 h₁
    have h9_18 : 9 ∣ 18 := by norm_num
    exact Nat.dvd_add h9_3n h9_18
  exact Nat.mod_eq_zero_of_dvd h9
