import Mathlib

open scoped Nat
open scoped Real

/--
The sum of the squares of three consecutive positive even numbers is $12296$. Find the product of the three numbers divided by $8$. -/
theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
  have h₂ : (3 : ℤ) * ↑n ^ 2 + 8 = 12296 := by
    have h₂ : (↑n - 2 : ℤ) ^ 2 + ↑n ^ 2 + (↑n + 2 : ℤ) ^ 2 = (3 : ℤ) * ↑n ^ 2 + 8 := by ring
    rw [h₂] at h₁
    exact h₁
  have h₃ : ↑n ^ 2 = 4096 := by linarith
  have h₄ : ↑n = 64 := by
    norm_cast at h₃
    have : n = 64 := by
      have : n ≤ 64 := by
        nlinarith
      have : n ≥ 64 := by
        nlinarith
      omega
    exact this
  rw [h₄]
  norm_num
