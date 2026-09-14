import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have hmod : (x : ZMod 11) ^ 5 = (y : ZMod 11) ^ 2 + 4 := by
    simpa [map_pow, map_add] using congrArg (Int.cast : ℤ → ZMod 11) h
  have h_no_sol : ∀ x y : ZMod 11, x ^ 5 ≠ y ^ 2 + 4 := by decide
  exact h_no_sol (x : ZMod 11) (y : ZMod 11) hmod
