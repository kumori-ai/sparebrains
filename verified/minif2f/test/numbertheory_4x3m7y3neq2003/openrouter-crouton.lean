import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have h2 : (4 : ZMod 7) * (x : ZMod 7) ^ 3 = 1 := by
    have hcast : ((4 * x ^ 3 - 7 * y ^ 3 : ℤ) : ZMod 7) = ((2003 : ℤ) : ZMod 7) := by
      rw [h]
    push_cast at hcast
    have h7 : (7 : ZMod 7) = 0 := by decide
    have h2003 : (2003 : ZMod 7) = 1 := by decide
    rw [h7, h2003] at hcast
    simpa using hcast
  have hall : ∀ a : ZMod 7, (4 : ZMod 7) * a ^ 3 ≠ 1 := by decide
  exact hall _ h2
