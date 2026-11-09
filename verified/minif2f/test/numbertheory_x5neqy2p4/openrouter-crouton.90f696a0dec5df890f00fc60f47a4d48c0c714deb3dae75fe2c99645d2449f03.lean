import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by
  intro h
  have h11 : (x : ZMod 11) ^ 5 = (y : ZMod 11) ^ 2 + 4 := by
    have h2 := congrArg (fun n : ℤ => (n : ZMod 11)) h
    push_cast at h2
    exact h2
  have hfin : ∀ a b : ZMod 11, a ^ 5 ≠ b ^ 2 + 4 := by decide
  exact hfin _ _ h11
