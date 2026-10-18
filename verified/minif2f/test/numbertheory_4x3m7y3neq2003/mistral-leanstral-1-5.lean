import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have hmod : (4 : ZMod 7) * ((x : ZMod 7) ^ 3) - (7 : ZMod 7) * ((y : ZMod 7) ^ 3) = (2003 : ZMod 7) := by
    simpa using congrArg (fun t : ℤ => (t : ZMod 7)) h
  have h7zero : (7 : ZMod 7) = 0 := by
    decide
  rw [h7zero, zero_mul, sub_zero] at hmod
  have h2003mod7 : (2003 : ZMod 7) = 1 := by
    decide
  rw [h2003mod7] at hmod
  have h_no_solution : ¬∃ (x : ZMod 7), (4 : ZMod 7) * x ^ 3 = 1 := by
    decide
  apply h_no_solution
  exact ⟨x, hmod⟩
