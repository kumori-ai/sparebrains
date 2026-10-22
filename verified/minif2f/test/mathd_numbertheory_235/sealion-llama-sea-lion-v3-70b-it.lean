import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $29 \cdot 79 + 31 \cdot 81$. -/
theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  have h1 : 29 * 79 % 10 = 1 := by
    have h1a : 29 % 10 = 9 := by
      norm_num
    have h1b : 79 % 10 = 9 := by
      norm_num
    have h1c : 9 * 9 % 10 = 1 := by
      norm_num
    exact h1c
  have h2 : 31 * 81 % 10 = 1 := by
    have h2a : 31 % 10 = 1 := by
      norm_num
    have h2b : 81 % 10 = 1 := by
      norm_num
    have h2c : 1 * 1 % 10 = 1 := by
      norm_num
    exact h2c
  have h3 : (1 + 1) % 10 = 2 := by
    norm_num
  exact h3
