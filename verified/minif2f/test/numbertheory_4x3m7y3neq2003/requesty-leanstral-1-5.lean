import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have hmod : (4 * x ^ 3 - 7 * y ^ 3 : ZMod 7) = (2003 : ZMod 7) := by
    simpa using congrArg (fun t : ℤ => (t : ZMod 7)) h
  have hmod' : (4 : ZMod 7) * ((x : ZMod 7) ^ 3) = 1 := by
    calc
      (4 : ZMod 7) * ((x : ZMod 7) ^ 3) = (4 * x ^ 3 - 7 * y ^ 3 : ZMod 7) := by
        push_cast
        have h7 : (7 : ZMod 7) = 0 := by decide
        rw [h7, zero_mul, sub_zero]
      _ = (2003 : ZMod 7) := hmod
      _ = 1 := by decide
  have hx_cube_eq_two : (x : ZMod 7) ^ 3 = 2 := by
    have h4inv : (4 : ZMod 7) * 2 = 1 := by decide
    calc
      (x : ZMod 7) ^ 3 = ((x : ZMod 7) ^ 3) * 1 := by ring
      _ = ((x : ZMod 7) ^ 3) * ((4 : ZMod 7) * 2) := by rw [h4inv]
      _ = (4 * (x : ZMod 7) ^ 3) * 2 := by ring
      _ = 1 * 2 := by rw [hmod']
      _ = 2 := by ring
  have h_no_cube : ∀ x : ZMod 7, x ^ 3 ≠ 2 := by
    decide
  exact h_no_cube (x : ZMod 7) hx_cube_eq_two
