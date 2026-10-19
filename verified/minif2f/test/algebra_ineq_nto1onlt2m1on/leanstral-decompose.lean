import Mathlib

open scoped Nat
open scoped Real

theorem algebra_ineq_nto1onlt2m1on (n : ℕ) (h₀ : n > 1) : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    positivity
  have hn_ge_2 : 2 ≤ n := by omega
  have hn_ge_2_real : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn_ge_2
  have h_pos : 0 < (n:ℝ) := hnpos
  have h32pos : 0 < (3:ℝ)/2 := by norm_num
  have h32gt1 : 1 < (3:ℝ)/2 := by norm_num
  have h_pow_ge_two (k : ℕ) (hk : 2 ≤ k) : (2:ℝ) ≤ ((3:ℝ)/2)^k := by
    refine Nat.le_induction ?base ?step k hk
    · norm_num
    · intro m hm IH
      rw [pow_succ]
      have hA : (2:ℝ) ≤ ((3:ℝ)/2)^m := IH
      have h_nonneg : 0 ≤ ((3:ℝ)/2)^m := pow_nonneg (by norm_num) _
      have h_three_halves_ge_one : (1:ℝ) ≤ (3:ℝ)/2 := by norm_num
      calc
        (2:ℝ) = 2 * 1 := by norm_num
        _ ≤ ((3:ℝ)/2)^m * 1 := mul_le_mul_of_nonneg_right hA (by norm_num)
        _ ≤ ((3:ℝ)/2)^m * ((3:ℝ)/2) := mul_le_mul_of_nonneg_left h_three_halves_ge_one h_nonneg
  have h_main : (n:ℝ) < ((3:ℝ)/2)^(n:ℕ) := by
    have h_base : ((2 : ℕ) : ℝ) < ((3/2 : ℝ) ^ (2 : ℕ)) := by
      norm_num
    have h_step : ∀ (k : ℕ), 2 ≤ k → ((k : ℝ) < ((3/2 : ℝ) ^ k)) → (((k+1 : ℕ) : ℝ) < ((3/2 : ℝ) ^ (k+1 : ℕ))) := by
      intro k hk2 hk
      have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have h_mul : (k+1 : ℝ) ≤ (3/2 : ℝ) * (k : ℝ) := by
        nlinarith
      have hpos32 : (0 : ℝ) < (3/2 : ℝ) := by norm_num
      have h_lt : (3/2 : ℝ) * (k : ℝ) < (3/2 : ℝ) * ((3/2 : ℝ) ^ k) :=
        mul_lt_mul_of_pos_left hk hpos32
      simpa [pow_succ, mul_comm] using (h_mul.trans_lt h_lt)
    have h_all : ∀ k : ℕ, 2 ≤ k → ((k : ℝ) < ((3/2 : ℝ) ^ k)) :=
      Nat.le_induction h_base h_step
    exact h_all n hn_ge_2
  have h_pos_inv : 0 < 1 / (n:ℝ) := div_pos (by norm_num) h_pos
  have h_base_nonneg : 0 ≤ (n:ℝ) := by linarith
  have h_rpow_lt : (n:ℝ) ^ (1 / (n:ℝ)) < (((3:ℝ)/2)^(n:ℕ)) ^ (1 / (n:ℝ)) :=
    Real.rpow_lt_rpow h_base_nonneg h_main h_pos_inv
  have h_simplify : (((3:ℝ)/2)^(n:ℕ)) ^ (1 / (n:ℝ)) = (3/2 : ℝ) := by
    calc
      (((3:ℝ)/2)^(n:ℕ)) ^ (1 / (n:ℝ)) = (((3:ℝ)/2)^(n:ℝ)) ^ (1 / (n:ℝ)) := by simp [Real.rpow_natCast]
      _ = ((3:ℝ)/2) ^ ((n:ℝ) * (1 / (n:ℝ))) := by
        rw [← Real.rpow_mul (show 0 ≤ (3:ℝ)/2 from by norm_num) (n:ℝ) (1 / (n:ℝ))]
      _ = ((3:ℝ)/2) ^ (1 : ℝ) := by
        field_simp [h_pos.ne']
      _ = (3/2 : ℝ) := by norm_num
  have h_lt_three_halves : (n:ℝ) ^ (1 / (n:ℝ)) < 3/2 := by
    linarith
  have h_inv_le : 1 / (n:ℝ) ≤ 1/2 := by
    exact (one_div_le_one_div h_pos (by norm_num)).mpr hn_ge_2_real
  linarith