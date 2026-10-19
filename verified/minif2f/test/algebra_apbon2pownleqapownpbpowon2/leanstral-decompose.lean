import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  induction' n with n ih;
  { simp [pow_zero] }
  have h_ab : 0 < a + b := add_pos h₀.left h₀.right;
  rcases h₀ with ⟨ha, hb⟩
  have ha' : 0 ≤ a := by linarith
  have hb' : 0 ≤ b := by linarith
  have hab' : 0 ≤ a + b := by linarith
  have hpos : 0 < (a + b) / (2 : ℝ) := by positivity
  have hpos' : 0 ≤ (a + b) / (2 : ℝ) := by linarith
  have hab_ne_zero : a + b ≠ 0 := by linarith
  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  cases n with
  | zero =>
      simp [pow_one]
  | succ n' =>
      set m := n' + 1 with hm
      have hm_pos : 0 < m := by
        dsimp [m]
        omega
      have ih_m : ((a + b) / (2 : ℝ)) ^ m ≤ (a ^ m + b ^ m) / (2 : ℝ) := by
        simpa using ih hm_pos
      have ha_nonneg : 0 ≤ a := by linarith
      have hb_nonneg : 0 ≤ b := by linarith
      have h_prod_nonneg : 0 ≤ (a ^ m - b ^ m) * (a - b) := by
        by_cases h : a ≤ b
        · have h1 : a - b ≤ 0 := by linarith
          have h2 : a ^ m - b ^ m ≤ 0 := by
            rw [sub_nonpos]
            exact pow_le_pow_left₀ ha' h m
          simpa using mul_nonneg_of_nonpos_of_nonpos h2 h1
        · have h' : b ≤ a := by linarith
          have h1 : 0 ≤ a - b := by linarith
          have h2 : 0 ≤ a ^ m - b ^ m := by
            rw [sub_nonneg]
            exact pow_le_pow_left₀ hb' h' m
          simpa using mul_nonneg h2 h1
      have h_ineq : (a + b) * (a ^ m + b ^ m) ≤ 2 * (a ^ (m + 1) + b ^ (m + 1)) := by
        have h_eq : 2 * (a ^ (m + 1) + b ^ (m + 1)) - (a + b) * (a ^ m + b ^ m) = (a ^ m - b ^ m) * (a - b) := by
          simp [pow_succ]
          nlinarith
        have h_nonneg : 0 ≤ 2 * (a ^ (m + 1) + b ^ (m + 1)) - (a + b) * (a ^ m + b ^ m) := by
          rw [h_eq]
          exact h_prod_nonneg
        linarith
      have h_main : ((a + b) / (2 : ℝ)) ^ (m + 1) ≤ (a ^ (m + 1) + b ^ (m + 1)) / (2 : ℝ) := by
        calc
          ((a + b) / (2 : ℝ)) ^ (m + 1) = ((a + b) / (2 : ℝ)) * ((a + b) / (2 : ℝ)) ^ m := by
            simp [pow_succ, mul_comm]
          _ ≤ ((a + b) / (2 : ℝ)) * ((a ^ m + b ^ m) / (2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left ih_m
            positivity
          _ = (a + b) * (a ^ m + b ^ m) / (4 : ℝ) := by
            field_simp
            linarith
          _ ≤ (a ^ (m + 1) + b ^ (m + 1)) / (2 : ℝ) := by
            linarith
      simpa [m] using h_main