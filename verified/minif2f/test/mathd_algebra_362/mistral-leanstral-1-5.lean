import Mathlib

open scoped Nat
open scoped Real

/--
If $a$ and $b$ are real numbers, $a^2b^3=\frac{32}{27}$, and $\frac{a}{b^3}=\frac{27}{4}$, what is $a+b$? -/
theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have hb3_ne_zero : b ^ 3 ≠ 0 := by
    intro hzero
    have : a / b ^ 3 = 0 := by simp [hzero]
    rw [this] at h₁
    norm_num at h₁
  set c := b ^ 3 with hc_def
  have ha_eq_c : a = (27/4) * c := by
    rw [hc_def]
    field_simp [hb3_ne_zero] at h₁
    linarith
  have hc_cube_eq : c ^ 3 = (8/27)^3 := by
    rw [hc_def] at h₀
    rw [ha_eq_c] at h₀
    ring_nf at h₀
    -- h₀: (729/16) * c ^ 3 = 32/27
    field_simp at h₀
    -- h₀: 729 * c ^ 3 * 27 = 32 * 16
    have htemp : c ^ 3 = 512/19683 := by
      nlinarith
    have h_rhs : (8/27)^3 = (512 : ℝ)/19683 := by norm_num
    linarith
  have hc_eq : c = 8/27 := by
    have h_factor : (c - 8/27) * (c^2 + (8/27)*c + (8/27)^2) = 0 := by
      have h_expand : (c - 8/27) * (c^2 + (8/27)*c + (8/27)^2) = c^3 - (8/27)^3 := by ring
      rw [h_expand]
      rw [hc_cube_eq]
      ring
    have h_pos : c^2 + (8/27)*c + (8/27)^2 > 0 := by
      have : c^2 + (8/27)*c + (8/27)^2 = (c + 4/27)^2 + 48/729 := by ring
      rw [this]
      positivity
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h | h
    · linarith
    · exfalso; linarith
  have ha_eq2 : a = 2 := by
    rw [ha_eq_c, hc_eq]
    ring
  have hb_eq : b = 2/3 := by
    rw [hc_def] at hc_eq
    -- hc_eq: b^3 = 8/27
    have h_factor2 : (b - 2/3) * (b^2 + (2/3)*b + 4/9) = 0 := by
      have h_expand2 : (b - 2/3) * (b^2 + (2/3)*b + 4/9) = b^3 - (2/3)^3 := by ring
      rw [h_expand2]
      rw [hc_eq]
      ring
    have h_pos2 : b^2 + (2/3)*b + 4/9 > 0 := by
      have : b^2 + (2/3)*b + 4/9 = (b + 1/3)^2 + 1/3 := by ring
      rw [this]
      positivity
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor2 with h | h
    · linarith
    · exfalso; linarith
  calc
    a + b = 2 + (2/3) := by rw [ha_eq2, hb_eq]
    _ = 8/3 := by ring
