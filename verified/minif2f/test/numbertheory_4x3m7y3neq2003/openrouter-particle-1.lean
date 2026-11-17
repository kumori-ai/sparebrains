import Mathlib

open scoped Nat
open scoped Real

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
  intro h
  have h' : (4 : ZMod 7) * (x : ZMod 7) ^ 3 - (7 : ZMod 7) * (y : ZMod 7) ^ 3 = (2003 : ZMod 7) := by
    have := congrArg (fun z : ℤ => (z : ZMod 7)) h
    push_cast at this
    simpa using this
  have h7zero : (7 : ZMod 7) = 0 := by decide
  have h2003 : (2003 : ZMod 7) = 1 := by decide
  rw [h7zero, h2003] at h'
  simp at h'
  have hno : ∀ z : ZMod 7, (4 : ZMod 7) * z ^ 3 ≠ 1 := by
    intro z
    fin_cases z <;> decide
  exact hno (x : ZMod 7) h'
