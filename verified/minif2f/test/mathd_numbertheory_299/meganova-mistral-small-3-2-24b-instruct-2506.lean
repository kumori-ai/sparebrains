import Mathlib

open scoped Nat
open scoped Real

/-- What is the ones digit of $1 \cdot 3 \cdot 5 \cdot 7 \cdot 9 \cdot 11 \cdot 13$? -/
theorem mathd_numbertheory_299 : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5 := by
  have h1 : 1 * 3 = 3 := by norm_num
  have h2 : 3 * 5 = 15 := by norm_num
  have h3 : 15 * 7 = 105 := by norm_num
  have h4 : 105 * 9 = 945 := by norm_num
  have h5 : 945 * 11 = 10395 := by norm_num
  have h6 : 10395 * 13 = 135135 := by norm_num
  have h7 : 135135 % 10 = 5 := by norm_num
  exact h7
