import Mathlib

open scoped Nat
open scoped Real

/-- What integer $n$ satisfies $0\le n<{101}$ and $$123456\equiv n\pmod {101}~?$$ -/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have h₂ : n ≤ 123456 := by omega
  have h₃ : (123456 - n) % 101 = 0 := Nat.mod_eq_zero_of_dvd h₁
  have h₄ : 123456 % 101 = n % 101 := by
    rw [← Nat.sub_add_cancel h₂, Nat.add_mod]
    simp [h₃]
  rw [Nat.mod_eq_of_lt h₀] at h₄
  norm_num at h₄
  omega
