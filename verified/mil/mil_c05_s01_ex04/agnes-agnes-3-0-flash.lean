import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 4. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex04 {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  have hm : 0 < m := Nat.pos_of_ne_zero mnez
  have hn : 0 < n := Nat.pos_of_ne_zero nnez
  rw [show (m * n).factorization = m.factorization + n.factorization from
    Nat.factorization_mul mnez nnez]
  simp [mul_comm]
