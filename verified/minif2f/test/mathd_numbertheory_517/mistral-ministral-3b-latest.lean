import Mathlib

open scoped Nat
open scoped Real

/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. -/
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  -- Compute each number modulo 4
  let n1 := 121 % 4
  let n2 := 122 % 4
  let n3 := 123 % 4
  -- Compute their values
  have h1 : n1 = 1 := by
    norm_num
  have h2 : n2 = 2 := by
    norm_num
  have h3 : n3 = 3 := by
    norm_num
  -- Compute intermediate products modulo 4
  have h4 : n1 * n2 % 4 = 1 * 2 % 4 := by
    rfl
  have h5 : (n1 * n2) * n3 % 4 = (1 * 2) * 3 % 4 := by
    rfl
  -- Compute the final product modulo 4
  have h6 : 1 * 2 * 3 % 4 = 6 % 4 := by
    norm_num
  -- Combine
  exact h6
