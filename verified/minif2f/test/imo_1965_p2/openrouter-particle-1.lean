import Mathlib

open scoped Nat
open scoped Real

/-- Consider the sytem of equations
 \[  a_{11}x_1+a_{12}x_2+a_{13}x_3 = 0 \]\[a_{21}x_1+a_{22}x_2+a_{23}x_3 =0\]\[a_{31}x_1+a_{32}x_2+a_{33}x_3 = 0   \] with unknowns $x_1, x_2, x_3$. The coefficients satisfy the conditions:

a) $a_{11}, a_{22}, a_{33}$ are positive numbers;

b) the remaining coefficients are negative numbers;

c) in each equation, the sum ofthe coefficients is positive.

Prove that the given system has only the solution $x_1=x_2=x_3=0$. -/
theorem imo_1965_p2 (x y z : ℝ) (a : ℕ → ℝ) (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
    (h₁ : a 1 < 0 ∧ a 2 < 0) (h₂ : a 3 < 0 ∧ a 5 < 0) (h₃ : a 6 < 0 ∧ a 7 < 0)
    (h₄ : 0 < a 0 + a 1 + a 2) (h₅ : 0 < a 3 + a 4 + a 5) (h₆ : 0 < a 6 + a 7 + a 8)
    (h₇ : a 0 * x + a 1 * y + a 2 * z = 0) (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
    (h₉ : a 6 * x + a 7 * y + a 8 * z = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx_zero (hxy : |y| ≤ |x|) (hxz : |z| ≤ |x|) : x = 0 := by
    have hA : 0 < a 0 := h₀.1
    have hB : a 1 < 0 := h₁.1
    have hC : a 2 < 0 := h₁.2
    have hBpos : 0 < -a 1 := by linarith
    have hCpos : 0 < -a 2 := by linarith
    have hx_eq : a 0 * x = (-a 1) * y + (-a 2) * z := by
      linarith [h₇]
    have h_abs_eq : a 0 * |x| = |(-a 1) * y + (-a 2) * z| := by
      calc
        a 0 * |x| = |a 0| * |x| := by rw [abs_of_pos hA]
        _ = |a 0 * x| := by rw [abs_mul]
        _ = |(-a 1) * y + (-a 2) * z| := by rw [hx_eq]
    have h_le : a 0 * |x| ≤ (-(a 1 + a 2)) * |x| := by
      calc
        a 0 * |x| = |(-a 1) * y + (-a 2) * z| := h_abs_eq
        _ ≤ |(-a 1) * y| + |(-a 2) * z| := abs_add_le _ _
        _ = (-a 1) * |y| + (-a 2) * |z| := by
          rw [abs_mul, abs_mul, abs_of_pos hBpos, abs_of_pos hCpos]
        _ ≤ (-a 1) * |x| + (-a 2) * |x| := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxy (le_of_lt hBpos)
          · exact mul_le_mul_of_nonneg_left hxz (le_of_lt hCpos)
        _ = (-(a 1 + a 2)) * |x| := by ring
    have hx_abs_zero : |x| = 0 := by
      by_contra h
      have hxpos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm h)
      have h_gt : (-(a 1 + a 2)) * |x| < a 0 * |x| := by
        have hrow : -(a 1 + a 2) < a 0 := by linarith [h₄]
        exact mul_lt_mul_of_pos_right hrow hxpos
      linarith [h_le, h_gt]
    exact abs_eq_zero.mp hx_abs_zero

  have hy_zero (hyx : |x| ≤ |y|) (hyz : |z| ≤ |y|) : y = 0 := by
    have hD : a 3 < 0 := h₂.1
    have hE : 0 < a 4 := h₀.2.1
    have hF : a 5 < 0 := h₂.2
    have hDpos : 0 < -a 3 := by linarith
    have hFpos : 0 < -a 5 := by linarith
    have hy_eq : a 4 * y = (-a 3) * x + (-a 5) * z := by
      linarith [h₈]
    have h_abs_eq : a 4 * |y| = |(-a 3) * x + (-a 5) * z| := by
      calc
        a 4 * |y| = |a 4| * |y| := by rw [abs_of_pos hE]
        _ = |a 4 * y| := by rw [abs_mul]
        _ = |(-a 3) * x + (-a 5) * z| := by rw [hy_eq]
    have h_le : a 4 * |y| ≤ (-(a 3 + a 5)) * |y| := by
      calc
        a 4 * |y| = |(-a 3) * x + (-a 5) * z| := h_abs_eq
        _ ≤ |(-a 3) * x| + |(-a 5) * z| := abs_add_le _ _
        _ = (-a 3) * |x| + (-a 5) * |z| := by
          rw [abs_mul, abs_mul, abs_of_pos hDpos, abs_of_pos hFpos]
        _ ≤ (-a 3) * |y| + (-a 5) * |y| := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hyx (le_of_lt hDpos)
          · exact mul_le_mul_of_nonneg_left hyz (le_of_lt hFpos)
        _ = (-(a 3 + a 5)) * |y| := by ring
    have hy_abs_zero : |y| = 0 := by
      by_contra h
      have hypos : 0 < |y| := lt_of_le_of_ne (abs_nonneg y) (Ne.symm h)
      have h_gt : (-(a 3 + a 5)) * |y| < a 4 * |y| := by
        have hrow : -(a 3 + a 5) < a 4 := by linarith [h₅]
        exact mul_lt_mul_of_pos_right hrow hypos
      linarith [h_le, h_gt]
    exact abs_eq_zero.mp hy_abs_zero

  have hz_zero (hzx : |x| ≤ |z|) (hzy : |y| ≤ |z|) : z = 0 := by
    have hG : a 6 < 0 := h₃.1
    have hH : a 7 < 0 := h₃.2
    have hI : 0 < a 8 := h₀.2.2
    have hGpos : 0 < -a 6 := by linarith
    have hHpos : 0 < -a 7 := by linarith
    have hz_eq : a 8 * z = (-a 6) * x + (-a 7) * y := by
      linarith [h₉]
    have h_abs_eq : a 8 * |z| = |(-a 6) * x + (-a 7) * y| := by
      calc
        a 8 * |z| = |a 8| * |z| := by rw [abs_of_pos hI]
        _ = |a 8 * z| := by rw [abs_mul]
        _ = |(-a 6) * x + (-a 7) * y| := by rw [hz_eq]
    have h_le : a 8 * |z| ≤ (-(a 6 + a 7)) * |z| := by
      calc
        a 8 * |z| = |(-a 6) * x + (-a 7) * y| := h_abs_eq
        _ ≤ |(-a 6) * x| + |(-a 7) * y| := abs_add_le _ _
        _ = (-a 6) * |x| + (-a 7) * |y| := by
          rw [abs_mul, abs_mul, abs_of_pos hGpos, abs_of_pos hHpos]
        _ ≤ (-a 6) * |z| + (-a 7) * |z| := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hzx (le_of_lt hGpos)
          · exact mul_le_mul_of_nonneg_left hzy (le_of_lt hHpos)
        _ = (-(a 6 + a 7)) * |z| := by ring
    have hz_abs_zero : |z| = 0 := by
      by_contra h
      have hzpos : 0 < |z| := lt_of_le_of_ne (abs_nonneg z) (Ne.symm h)
      have h_gt : (-(a 6 + a 7)) * |z| < a 8 * |z| := by
        have hrow : -(a 6 + a 7) < a 8 := by linarith [h₆]
        exact mul_lt_mul_of_pos_right hrow hzpos
      linarith [h_le, h_gt]
    exact abs_eq_zero.mp hz_abs_zero

  by_cases hxy : |x| ≤ |y|
  · by_cases hyz : |y| ≤ |z|
    · have hz : z = 0 := hz_zero (le_trans hxy hyz) hyz
      have hy : y = 0 := hy_zero hxy (by simpa [hz] using (abs_nonneg y))
      have hx : x = 0 := by
        have : |x| ≤ 0 := by simpa [hy] using hxy
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg x))
      exact ⟨hx, hy, hz⟩
    · have hzy : |z| ≤ |y| := le_of_lt (lt_of_not_ge hyz)
      have hy : y = 0 := hy_zero hxy hzy
      have hx : x = 0 := by
        have : |x| ≤ 0 := by simpa [hy] using hxy
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg x))
      have hz : z = 0 := hz_zero (by simpa [hx] using (abs_nonneg z))
        (by simpa [hy] using (abs_nonneg z))
      exact ⟨hx, hy, hz⟩
  · have hyx : |y| < |x| := lt_of_not_ge hxy
    by_cases hxz : |x| ≤ |z|
    · have hz : z = 0 := hz_zero hxz (le_trans (le_of_lt hyx) hxz)
      have hx : x = 0 := hx_zero (le_of_lt hyx) (by simpa [hz] using (abs_nonneg x))
      have hy : y = 0 := by
        have : |y| < 0 := by simpa [hx] using hyx
        exact False.elim (not_lt_of_ge (abs_nonneg y) this)
      exact ⟨hx, hy, hz⟩
    · have hzx : |z| < |x| := lt_of_not_ge hxz
      have hx : x = 0 := hx_zero (le_of_lt hyx) (le_of_lt hzx)
      have : |y| < 0 := by simpa [hx] using hyx
      exact False.elim (not_lt_of_ge (abs_nonneg y) this)
