import Mathlib

open scoped Nat
open scoped Real

/--
Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? -/
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h₃ : (x : ℤ) + (y : ℤ) = 36 := by
    ring_nf at h₂ ⊢
    omega
  have h₄ : x + y = 36 := by
    exact_mod_cast h₃
  have h₅ : x + 5 * x = 36 := by
    rw [← h₁] at h₄
    exact h₄
  omega
