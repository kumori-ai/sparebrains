import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have h' : ((x : ZMod 11) ^ 5) = (y : ZMod 11) ^ 2 + 4 := by
    have := congrArg (fun z : ℤ => (z : ZMod 11)) h
    simpa using this
  have hmod : ∀ a b : ZMod 11, a ^ 5 ≠ b ^ 2 + 4 := by
    decide
  exact hmod (x : ZMod 11) (y : ZMod 11) h'
