import Mathlib

open scoped Nat
open scoped Real

theorem algebra_ineq_nto1onlt2m1on (n : ℕ) (h₀ : n > 1) : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hN_pos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hN_ne : ((m + 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt hN_pos
  have h_inv_lt : 1 / ((m + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one hN_pos]
    exact_mod_cast (by omega : 1 < m + 2)
  set a : ℝ := 1 - 1 / ((m + 2 : ℕ) : ℝ) with ha_def
  have ha_pos : 0 < a := by linarith
  have hy_eq : 2 - 1 / ((m + 2 : ℕ) : ℝ) = 1 + a := by ring
  have hy_pos : 0 < 2 - 1 / ((m + 2 : ℕ) : ℝ) := by linarith
  have bernoulli : ∀ k : ℕ, 1 + (k : ℝ) * a ≤ (1 + a) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have h1 : (1 + (k : ℝ) * a) * (1 + a) ≤ (1 + a) ^ k * (1 + a) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      have h2 : 1 + ((k + 1 : ℕ) : ℝ) * a ≤ (1 + (k : ℝ) * a) * (1 + a) := by
        have heq : (1 + (k : ℝ) * a) * (1 + a)
            = 1 + ((k + 1 : ℕ) : ℝ) * a + (k : ℝ) * a ^ 2 := by
          push_cast
          ring
        rw [heq]
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hnn : 0 ≤ (k : ℝ) * a ^ 2 := mul_nonneg hk (sq_nonneg a)
        linarith
      linarith
  have h_pow : ((m + 2 : ℕ) : ℝ) < (2 - 1 / ((m + 2 : ℕ) : ℝ)) ^ (m + 2) := by
    have h1 : (2 - 1 / ((m + 2 : ℕ) : ℝ)) ^ (m + 2)
        = (2 - 1 / ((m + 2 : ℕ) : ℝ)) ^ (m + 1) * (2 - 1 / ((m + 2 : ℕ) : ℝ)) :=
      pow_succ _ _
    rw [h1, hy_eq]
    have hb := bernoulli (m + 1)
    have hge : (1 + ((m + 1 : ℕ) : ℝ) * a) * (1 + a)
        ≤ (1 + a) ^ (m + 1) * (1 + a) :=
      mul_le_mul_of_nonneg_right hb (by linarith)
    have hN_eq2 : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have hna : ((m + 2 : ℕ) : ℝ) * a = ((m + 2 : ℕ) : ℝ) - 1 := by
      rw [ha_def]
      field_simp
    have hlb : ((m + 2 : ℕ) : ℝ) < (1 + ((m + 1 : ℕ) : ℝ) * a) * (1 + a) := by
      have heq : (1 + ((m + 1 : ℕ) : ℝ) * a) * (1 + a)
          = ((m + 2 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * a ^ 2 := by
        calc (1 + ((m + 1 : ℕ) : ℝ) * a) * (1 + a)
            = 1 + (((m + 1 : ℕ) : ℝ) + 1) * a + ((m + 1 : ℕ) : ℝ) * a ^ 2 := by ring
          _ = 1 + ((m + 2 : ℕ) : ℝ) * a + ((m + 1 : ℕ) : ℝ) * a ^ 2 := by rw [← hN_eq2]
          _ = ((m + 2 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * a ^ 2 := by rw [hna]; ring
      rw [heq]
      have ht : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hprod : 0 < ((m + 1 : ℕ) : ℝ) * a ^ 2 := mul_pos ht (pow_pos ha_pos 2)
      linarith
    linarith
  have hx_pow : (((m + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ))) ^ (m + 2)
      = ((m + 2 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast (((m + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ))) (m + 2),
      ← Real.rpow_mul hN_pos.le]
    have h1 : (1 / ((m + 2 : ℕ) : ℝ)) * ((m + 2 : ℕ) : ℝ) = 1 := one_div_mul_cancel hN_ne
    rw [h1, Real.rpow_one]
  by_contra h
  have hle : 2 - 1 / ((m + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) :=
    le_of_not_gt h
  have hle_pow : (2 - 1 / ((m + 2 : ℕ) : ℝ)) ^ (m + 2)
      ≤ (((m + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ))) ^ (m + 2) :=
    pow_le_pow_left₀ hy_pos.le hle (m + 2)
  rw [hx_pow] at hle_pow
  linarith
