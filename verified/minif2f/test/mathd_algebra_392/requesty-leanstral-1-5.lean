import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  rcases h₀ with ⟨k, hk⟩
  have hkz : (n : ℤ) = 2 * (k : ℤ) := by
    simpa [two_mul] using mod_cast hk
  rw [hkz] at h₁ ⊢
  have hk_nonneg : 0 ≤ (k : ℤ) := Nat.cast_nonneg _
  have hk_sq : (k : ℤ)^2 = 1024 := by
    nlinarith
  have hk_eq_32 : (k : ℤ) = 32 := by
    nlinarith
  rw [hk_eq_32]
  norm_num
