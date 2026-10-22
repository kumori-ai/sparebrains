import Mathlib

open scoped Nat
open scoped Real

/-- What integer $n$ satisfies $0\le n<{101}$ and $$123456\equiv n\pmod {101}~?$$ -/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have h₂ : n ≤ 123456 := by
    omega
  have h₃ : n % 101 = 123456 % 101 := by
    omega
  have h₄ : 123456 % 101 = 34 := by
    norm_num
  have h₅ : n % 101 = 34 := by
    rw [h₃, h₄]
  have h₆ : n = 34 := by
    by_contra h
    have h₇ : n ≠ 34 := by
      exact h
    have h₈ : n % 101 ≠ 34 := by
      by_contra h₉
      simp_all
      omega
    omega
  exact h₆
