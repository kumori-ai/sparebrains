import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have hmod : (x : ZMod 11) ^ 5 = (y : ZMod 11) ^ 2 + 4 := by
    simpa using congrArg (fun t : ℤ => (t : ZMod 11)) h
  have no_solutions : ∀ (a b : ZMod 11), a ^ 5 ≠ b ^ 2 + 4 := by
    decide
  exact no_solutions (x : ZMod 11) (y : ZMod 11) hmod
