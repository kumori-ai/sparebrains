import Mathlib

open scoped Nat
open scoped Real

/--
If $a$ and $b$ are real numbers, $a^2b^3=\frac{32}{27}$, and $\frac{a}{b^3}=\frac{27}{4}$, what is $a+b$? -/
theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have hb_ne : b ≠ 0 := by
    intro hb
    rw [hb] at h₀
    norm_num at h₀
  have hb3_ne : b ^ 3 ≠ 0 := pow_ne_zero 3 hb_ne
  have ha_eq : a = 27 / 4 * b ^ 3 := (div_eq_iff hb3_ne).mp h₁
  rw [ha_eq] at h₀
  have h_b9 : b ^ 9 = (2 / 3 : ℝ) ^ 9 := by
    have h_eq : b ^ 9 = 512 / 19683 := by
      linear_combination (16 / 729 : ℝ) * h₀
    rw [h_eq]
    norm_num
  have hb_eq : b = 2 / 3 := by
    rcases lt_trichotomy b (2 / 3) with hlt | heq | hgt
    · exfalso
      by_cases hb_nonneg : 0 ≤ b
      · have hlt9 : b ^ 9 < (2 / 3 : ℝ) ^ 9 :=
          pow_lt_pow_left₀ hlt hb_nonneg (by norm_num)
        linarith
      · push_neg at hb_nonneg
        have hb4_ne : b ^ 4 ≠ 0 := pow_ne_zero 4 hb_ne
        have hb8_pos : 0 < b ^ 8 := by
          rw [show b ^ 8 = (b ^ 4) ^ 2 by ring]
          exact sq_pos_of_ne_zero hb4_ne
        have hb9_neg : b ^ 9 < 0 := by
          rw [show b ^ 9 = b * b ^ 8 by ring]
          exact mul_neg_of_neg_of_pos hb_nonneg hb8_pos
        have hpos : (0 : ℝ) < (2 / 3 : ℝ) ^ 9 := by positivity
        linarith
    · exact heq
    · exfalso
      have hgt9 : (2 / 3 : ℝ) ^ 9 < b ^ 9 :=
        pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
      linarith
  rw [ha_eq, hb_eq]
  norm_num
