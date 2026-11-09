import Mathlib

open scoped Nat
open scoped Real

/-- What is the sum of the final three digits of the integer representation of $5^{100}$? -/
theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by
  have hpow : ∀ k : ℕ, 625 ^ (k + 1) % 1000 = 625 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have h5 : 5 ^ 100 = 625 ^ 25 := by
    calc 5 ^ 100 = 5 ^ (4 * 25) := by norm_num
      _ = (5 ^ 4) ^ 25 := by rw [pow_mul]
      _ = 625 ^ 25 := by norm_num
  have hmod : 5 ^ 100 % 1000 = 625 := by
    rw [h5]
    exact hpow 24
  have hd : Nat.digits 10 625 = [5, 2, 6] := by
    norm_num [Nat.digits_def', Nat.digits_of_lt]
  rw [hmod, hd] at h₁
  simp at h₁
  omega
