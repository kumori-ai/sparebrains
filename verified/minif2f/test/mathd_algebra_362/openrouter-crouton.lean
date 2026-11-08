import Mathlib

open scoped Nat
open scoped Real

/--
If $a$ and $b$ are real numbers, $a^2b^3=\frac{32}{27}$, and $\frac{a}{b^3}=\frac{27}{4}$, what is $a+b$? -/
theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by
  have cube_inj : ∀ x y : ℝ, y ≠ 0 → x ^ 3 = y ^ 3 → x = y := by
    intro x y hy h
    have hy2 : 0 < y ^ 2 := pow_two_pos_of_ne_zero hy
    have hsecond : 0 < x ^ 2 + x * y + y ^ 2 := by
      nlinarith [sq_nonneg (x + y / 2), hy2]
    have hfact : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
      have h0 : x ^ 3 - y ^ 3 = 0 := sub_eq_zero.mpr h
      have hring : (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 := by ring
      rw [hring, h0]
    rcases mul_eq_zero.mp hfact with h1 | h1
    · exact sub_eq_zero.mp h1
    · linarith
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0] at h₀
    simp at h₀
    norm_num at h₀
  have hb3 : b ^ 3 ≠ 0 := pow_ne_zero 3 hb
  have ha_eq : a = 27 / 4 * b ^ 3 := by
    rw [div_eq_iff hb3] at h₁
    exact h₁
  have hcube : (b ^ 3) ^ 3 = (8 / 27 : ℝ) ^ 3 := by
    have h := h₀
    rw [ha_eq] at h
    have h2 : (27 / 4 * b ^ 3) ^ 2 * b ^ 3 = (729 / 16) * (b ^ 3) ^ 3 := by ring
    rw [h2] at h
    have hR : (8 / 27 : ℝ) ^ 3 = 512 / 19683 := by norm_num
    rw [hR]
    linarith [h]
  have hb3_eq : b ^ 3 = 8 / 27 := cube_inj (b ^ 3) (8 / 27) (by norm_num) hcube
  have hb_eq : b = 2 / 3 := by
    apply cube_inj b (2 / 3) (by norm_num)
    rw [hb3_eq]
    norm_num
  rw [ha_eq, hb3_eq, hb_eq]
  norm_num
