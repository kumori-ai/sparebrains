import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  obtain ⟨ha, hb⟩ := h₀
  have key : ∀ n : ℕ, 1 ≤ n → ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hm : 0 ≤ (a + b) / 2 := by linarith
      have hprod : 0 ≤ (a - b) * (a ^ n - b ^ n) := by
        rcases le_total a b with hab | hab
        · have h1 : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha.le hab n
          exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab) (sub_nonpos.mpr h1)
        · have h1 : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb.le hab n
          exact mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h1)
      have h1 : ((a + b) / 2) ^ (n + 1) ≤ ((a ^ n + b ^ n) / 2) * ((a + b) / 2) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih hm
      have h2 : ((a ^ n + b ^ n) / 2) * ((a + b) / 2) ≤ (a ^ (n + 1) + b ^ (n + 1)) / 2 := by
        rw [pow_succ', pow_succ']
        nlinarith [hprod]
      exact le_trans h1 h2
  exact key n h₁
