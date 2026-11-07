import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 6. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex06 {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
