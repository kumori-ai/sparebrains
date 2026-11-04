import Mathlib

/-- Mathematics in Lean, Chapter 5 §1 (Irrational Roots), exercise 5. Avigad & Massot, Apache-2.0, commit dd6d752. -/
theorem mil_c05_s01_ex05 (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  simpa using congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_pow n k)
