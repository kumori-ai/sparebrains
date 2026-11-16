import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have ha : 0 ≤ a := le_of_lt h₀.1
  have hb : 0 ≤ b := le_of_lt h₀.2
  have hsum : 0 ≤ (a + b) / 2 := by positivity
  have hmain : ∀ n : ℕ, ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hmono : 0 ≤ (a - b) * (a ^ n - b ^ n) := by
          rcases le_total a b with hab | hba
          · have hpow : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha hab n
            exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab) (sub_nonpos.mpr hpow)
          · have hpow : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb hba n
            exact mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hpow)
        have h2 : ((a + b) / 2) ^ (n + 1) ≤ ((a ^ n + b ^ n) / 2) * ((a + b) / 2) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right ih hsum
        have h3 : ((a ^ n + b ^ n) / 2) * ((a + b) / 2) ≤ (a ^ (n + 1) + b ^ (n + 1)) / 2 := by
          rw [pow_succ, pow_succ]
          nlinarith [hmono]
        exact le_trans h2 h3
  exact hmain n
