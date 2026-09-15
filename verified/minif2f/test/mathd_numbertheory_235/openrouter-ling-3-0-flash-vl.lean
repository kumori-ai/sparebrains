import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $29 \cdot 79 + 31 \cdot 81$. -/
theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  norm_num
