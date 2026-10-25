import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have h_mod : ((x : ℤ) ^ 5 : ZMod 11) = ((y : ℤ) ^ 2 + 4 : ZMod 11) := by
    simpa using congrArg (fun t : ℤ => (t : ZMod 11)) h
  have h_mod' : ((x : ZMod 11) ^ 5) = ((y : ZMod 11) ^ 2 + 4) := by
    simpa using h_mod
  have h_all : ∀ (a b : ZMod 11), a ^ 5 ≠ b ^ 2 + 4 := by
    decide
  exact h_all (x : ZMod 11) (y : ZMod 11) h_mod'
