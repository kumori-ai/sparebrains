import Mathlib

open scoped Nat
open scoped Real

/-- Find the modulo 4 residue of $121 \cdot 122 \cdot 123$. -/
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
  have h1 : 121 % 4 = 1 := by simp
  have h2 : 122 % 4 = 2 := by simp
  have h3 : 123 % 4 = 3 := by simp
  have h4 : 1 * 2 * 3 % 4 = 2 := by simp
  have h5 : 121 * 122 * 123 % 4 = 1 * 2 * 3 % 4 := by simp [h1, h2, h3]
  exact h5
