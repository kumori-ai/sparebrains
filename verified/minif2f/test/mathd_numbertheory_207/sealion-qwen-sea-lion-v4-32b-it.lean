import Mathlib

open scoped Nat
open scoped Real

/-- Convert $852_9$ to base 10. -/
theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
  calc
  8 * 9 ^ 2 + 5 * 9 + 2 = 8 * (9 * 9) + 5 * 9 + 2 := by rw [Nat.pow_two]
  _ = 8 * 81 + 5 * 9 + 2 := by simp
  _ = 648 + 45 + 2 := by simp
  _ = 695 := by ring
