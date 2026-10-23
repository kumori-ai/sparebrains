import Mathlib

open scoped Nat
open scoped Real

/-- What is the ones digit of $1 \cdot 3 \cdot 5 \cdot 7 \cdot 9 \cdot 11 \cdot 13$? -/
theorem mathd_numbertheory_299 : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5 := by
  have h1 : 1 * 3 * 5 * 7 * 9 * 11 * 13 = 135135 := by
    calc
      1 * 3 * 5 * 7 * 9 * 11 * 13 = (1 * 3) * 5 * 7 * 9 * 11 * 13 := by simp [Nat.mul_assoc]
      _ = 3 * 5 * 7 * 9 * 11 * 13 := by simp [Nat.mul_one]
      _ = (3 * 5) * 7 * 9 * 11 * 13 := by simp [Nat.mul_assoc]
      _ = 15 * 7 * 9 * 11 * 13 := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ = (15 * 7) * 9 * 11 * 13 := by simp [Nat.mul_assoc]
      _ = 105 * 9 * 11 * 13 := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ = (105 * 9) * 11 * 13 := by simp [Nat.mul_assoc]
      _ = 945 * 11 * 13 := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ = (945 * 11) * 13 := by simp [Nat.mul_assoc]
      _ = 10395 * 13 := by simp [Nat.mul_comm, Nat.mul_assoc]
      _ = 135135 := by simp [Nat.mul_comm, Nat.mul_assoc]
  have h2 : 135135 % 10 = 5 := by
    simp [Nat.mod_eq_of_lt, Nat.lt_succ_iff, Nat.mod_def, Nat.div_eq_of_lt]
  rw [h1, h2]
