import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex04 {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl
