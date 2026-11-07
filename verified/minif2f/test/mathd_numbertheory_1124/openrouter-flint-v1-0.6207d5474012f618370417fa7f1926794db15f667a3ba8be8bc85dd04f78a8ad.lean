import Mathlib

open scoped Nat
open scoped Real

/-- The four-digit number $\underline{374n}$ is divisible by 18. Find the units digit $n$. -/
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
  norm_num at h₁
  rcases h₁ with ⟨k, hk⟩
  norm_num at hk
  have hk_le : k ≤ 208 := by
    have h : 18 * k ≤ 3749 := by
      rw [← hk]
      omega
    nlinarith
  have hk_ge : k ≥ 208 := by
    have h : 18 * k ≥ 3740 := by
      rw [← hk]
      omega
    nlinarith
  have hk_eq : k = 208 := by omega
  subst k
  norm_num at hk
  omega
