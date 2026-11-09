import Mathlib

open scoped Nat
open scoped Real

/-- Find the remainder when $1 + 2 + 2^2 + 2^3 + \dots + 2^{100}$ is divided by 7. -/
theorem mathd_numbertheory_127 : (∑ k ∈ Finset.range 101, 2 ^ k) % 7 = 3 := by
  have hpow : (2 : ZMod 7) ^ 101 = 4 := by
    have h3 : (2 : ZMod 7) ^ 3 = 1 := by decide
    have h101 : (101 : ℕ) = 3 * 33 + 2 := rfl
    rw [h101, pow_add, pow_mul, h3]
    decide
  have hcast : ((∑ k ∈ Finset.range 101, 2 ^ k : ℕ) : ZMod 7) = 3 := by
    push_cast
    have h := geom_sum_mul (2 : ZMod 7) 101
    rw [hpow] at h
    have h21 : (2 : ZMod 7) - 1 = 1 := by decide
    rw [h21, mul_one] at h
    have h41 : (4 : ZMod 7) - 1 = 3 := by decide
    rw [h41] at h
    exact h
  have hmodeq : (∑ k ∈ Finset.range 101, 2 ^ k) ≡ 3 [MOD 7] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    exact_mod_cast hcast
  exact hmodeq
