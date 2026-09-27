import Mathlib

open scoped Nat
open scoped Real

/-- What integer $n$ satisfies $0\le n<{101}$ and $$123456\equiv n\pmod {101}~?$$ -/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  rcases h₁ with ⟨k, hk⟩
  omega
