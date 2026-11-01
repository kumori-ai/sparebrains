import Mathlib

open scoped Nat
open scoped Real

/-- The four-digit number $\underline{374n}$ is divisible by 18. Find the units digit $n$. -/
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
  have h₂ : (374 * 10 + n) % 18 = 0 := Nat.mod_eq_zero_of_dvd h₁
  norm_num at h₂
  omega
