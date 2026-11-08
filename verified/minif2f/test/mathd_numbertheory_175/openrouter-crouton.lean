import Mathlib

open scoped Nat
open scoped Real

/-- What is the units digit of $2^{2010}$? -/
theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by
  have h1 : ∀ n : ℕ, (6 : ZMod 10) ^ (n + 1) = 6 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc (6 : ZMod 10) ^ (k + 1 + 1) = (6 : ZMod 10) ^ (k + 1) * 6 := by ring
        _ = 6 * 6 := by rw [ih]
        _ = 6 := by decide
  have h2 : (2 : ZMod 10) ^ 2010 = 4 := by
    calc (2 : ZMod 10) ^ 2010 = (2 : ZMod 10) ^ (4 * 502 + 2) := by
          rw [show (2010 : ℕ) = 4 * 502 + 2 by norm_num]
      _ = ((2 : ZMod 10) ^ 4) ^ 502 * (2 : ZMod 10) ^ 2 := by
          rw [pow_add, pow_mul]
      _ = (6 : ZMod 10) ^ 502 * 4 := by
          rw [show (2 : ZMod 10) ^ 4 = 6 by decide, show (2 : ZMod 10) ^ 2 = 4 by decide]
      _ = 6 * 4 := by
          rw [show (6 : ZMod 10) ^ 502 = 6 from h1 501]
      _ = 4 := by decide
  have h3 : ((2 ^ 2010 : ℕ) : ZMod 10) = ((4 : ℕ) : ZMod 10) := by exact_mod_cast h2
  have h4 : 2 ^ 2010 ≡ 4 [MOD 10] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
  have h5 : 2 ^ 2010 % 10 = 4 % 10 := h4
  rw [show (4 : ℕ) % 10 = 4 by decide] at h5
  exact h5
