import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have h' : (x : ZMod 11) ^ 5 = (y : ZMod 11) ^ 2 + 4 := by
    have hcast := congrArg (fun n : ℤ => (n : ZMod 11)) h
    push_cast at hcast
    exact hcast
  have hcontra : ∀ a b : ZMod 11, a ^ 5 ≠ b ^ 2 + 4 := by decide
  exact hcontra _ _ h'
