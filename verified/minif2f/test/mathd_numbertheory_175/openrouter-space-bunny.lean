import Mathlib

open scoped Nat
open scoped Real

/-- What is the units digit of $2^{2010}$? -/
theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by
  have hcycle : ∀ k : ℕ, 2 ^ (4 * k + 2) % 10 = 4 := by
    intro k
    induction k with
    | zero =>
        norm_num
    | succ k ih =>
        rw [show 4 * (k + 1) + 2 = (4 * k + 2) + 4 by omega,
          pow_add, Nat.mul_mod, ih]
        norm_num
  simpa [show 2010 = 4 * 502 + 2 by omega] using hcycle 502
