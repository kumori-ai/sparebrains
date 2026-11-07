import Mathlib

open scoped Nat
open scoped Real

/-- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
  have h : ((16 ^ 17 * 17 ^ 18 * 18 ^ 19 : ℕ) : ZMod 10) = ((8 : ℕ) : ZMod 10) := by decide
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact h2
