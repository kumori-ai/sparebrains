import Mathlib

open scoped Nat
open scoped Real

/-- Given $2^a = 32$ and $a^b = 125$ find $b^a$. -/
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  have h5 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have ha : a = 5 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) h
      rw [h₀, h5] at hlt
      norm_num at hlt
    · have hlt := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) h
      rw [h₀, h5] at hlt
      norm_num at hlt
  subst ha
  have h53 : (5 : ℝ) ^ (3 : ℝ) = 125 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hb : b = 3 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 5 by norm_num) h
      rw [h₁, h53] at hlt
      norm_num at hlt
    · have hlt := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 5 by norm_num) h
      rw [h₁, h53] at hlt
      norm_num at hlt
  subst hb
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num
