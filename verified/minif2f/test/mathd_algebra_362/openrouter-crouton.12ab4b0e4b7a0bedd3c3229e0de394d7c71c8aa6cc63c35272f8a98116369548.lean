import Mathlib

open scoped Nat
open scoped Real

/--
If $a$ and $b$ are real numbers, $a^2b^3=\frac{32}{27}$, and $\frac{a}{b^3}=\frac{27}{4}$, what is $a+b$? -/
theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have hb3 : b ^ 3 ≠ 0 := by
    intro h
    rw [h, div_zero] at h₁
    norm_num at h₁
  have ha : a = 27 / 4 * b ^ 3 := (div_eq_iff hb3).mp h₁
  have h2 : (27 / 4 * b ^ 3) ^ 2 * b ^ 3 = 32 / 27 := by
    rw [← ha]
    exact h₀
  have h3 : (b ^ 3) ^ 3 = (8 / 27 : ℝ) ^ 3 := by
    linear_combination (16 / 729) * h2
  have hfactor : (b ^ 3 - 8 / 27) * ((b ^ 3) ^ 2 + b ^ 3 * (8 / 27) + (8 / 27) ^ 2) = 0 := by
    have h : (b ^ 3 - 8 / 27) * ((b ^ 3) ^ 2 + b ^ 3 * (8 / 27) + (8 / 27) ^ 2)
        = (b ^ 3) ^ 3 - (8 / 27) ^ 3 := by ring
    rw [h, h3, sub_self]
  have hpos : (b ^ 3) ^ 2 + b ^ 3 * (8 / 27) + (8 / 27) ^ 2 > 0 := by
    nlinarith [sq_nonneg (b ^ 3 + 4 / 27)]
  have hb3eq : b ^ 3 = 8 / 27 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  have h4 : b ^ 3 = (2 / 3 : ℝ) ^ 3 := by
    rw [hb3eq]
    norm_num
  have hfactor2 : (b - 2 / 3) * (b ^ 2 + b * (2 / 3) + (2 / 3) ^ 2) = 0 := by
    have h : (b - 2 / 3) * (b ^ 2 + b * (2 / 3) + (2 / 3) ^ 2) = b ^ 3 - (2 / 3) ^ 3 := by ring
    rw [h, h4, sub_self]
  have hpos2 : b ^ 2 + b * (2 / 3) + (2 / 3) ^ 2 > 0 := by
    nlinarith [sq_nonneg (b + 1 / 3)]
  have hb : b = 2 / 3 := by
    rcases mul_eq_zero.mp hfactor2 with h | h
    · linarith
    · linarith
  rw [ha, hb3eq, hb]
  norm_num
