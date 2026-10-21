import Mathlib

open scoped Nat
open scoped Real

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
    ∏ k ∈ Finset.Icc 1 n, (1 + (1 : ℝ) / k ^ 3) ≤ (3 : ℝ) - 1 / ↑n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hzero : n = 0
    · subst hzero
      norm_num
    · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
      have ih_n := ih hpos
      have hle : (1 : ℕ) ≤ n + 1 := by omega
      have hpos_n : (0 : ℝ) < n := by exact_mod_cast hpos
      have hpos_succ : (0 : ℝ) < (n + (1 : ℕ) : ℝ) := by exact_mod_cast h₀
      have hP_nonneg : 0 ≤ ∏ k ∈ Finset.Icc (1 : ℕ) n, ((1 : ℝ) + (1 : ℝ) / ↑k ^ (3 : ℕ)) := by
        refine Finset.prod_nonneg (fun k hk => ?_)
        positivity
      have hterm_nonneg : 0 ≤ (1 : ℝ) + (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ^ 3 := by
        positivity
      have hprod_split : ∏ k ∈ Finset.Icc (1 : ℕ) (n + (1 : ℕ)), ((1 : ℝ) + (1 : ℝ) / ↑k ^ (3 : ℕ)) =
          (∏ k ∈ Finset.Icc (1 : ℕ) n, ((1 : ℝ) + (1 : ℝ) / ↑k ^ (3 : ℕ))) * ((1 : ℝ) + (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ^ 3) := by
        rw [Finset.prod_Icc_succ_top hle]
      rw [hprod_split]
      have h_mul : (∏ k ∈ Finset.Icc (1 : ℕ) n, ((1 : ℝ) + (1 : ℝ) / ↑k ^ (3 : ℕ))) * ((1 : ℝ) + (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ^ 3) ≤
          (3 - 1 / (n : ℝ)) * ((1 : ℝ) + (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_right ih_n hterm_nonneg
      have h_ineq : (3 - 1 / (n : ℝ)) * ((1 : ℝ) + (1 : ℝ) / (↑(n + (1 : ℕ)) : ℝ) ^ 3) ≤ 3 - 1 / (↑(n + (1 : ℕ)) : ℝ) := by
        field_simp [hpos_n.ne.symm, hpos_succ.ne.symm, pow_ne_zero 3 hpos_succ.ne.symm]
        push_cast
        have h : (n : ℝ)^2 - (n : ℝ) + 2 ≥ 0 := by
          have : (n : ℝ)^2 - (n : ℝ) + 2 = ((n : ℝ) - 1/2)^2 + 7/4 := by ring
          rw [this]
          positivity
        nlinarith
      exact le_trans h_mul h_ineq