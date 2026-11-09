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
  have key1 : |y| ≤ |x| → |z| ≤ |x| → x = 0 := by
    intro hy hz
    by_cases hx : x = 0
    · exact hx
    · exfalso
      have hpos : 0 < |x| := abs_pos.mpr hx
      have h1 : a 0 * |x| = |a 0 * x| := by rw [abs_mul, abs_of_pos h₀.1]
      have h2 : |a 0 * x| ≤ (-a 1) * |x| + (-a 2) * |x| := by
        have heq : a 0 * x = -(a 1 * y + a 2 * z) := by linarith [h₇]
        rw [heq, abs_neg]
        calc |a 1 * y + a 2 * z| ≤ |a 1 * y| + |a 2 * z| := abs_add_le _ _
          _ = (-a 1) * |y| + (-a 2) * |z| := by
              rw [abs_mul, abs_mul, abs_of_neg h₁.1, abs_of_neg h₁.2]
          _ ≤ (-a 1) * |x| + (-a 2) * |x| := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hy (by linarith [h₁.1])
              · exact mul_le_mul_of_nonneg_left hz (by linarith [h₁.2])
      have h3 : (-a 1) * |x| + (-a 2) * |x| < a 0 * |x| := by
        calc (-a 1) * |x| + (-a 2) * |x| = ((-a 1) + (-a 2)) * |x| := by ring
          _ < a 0 * |x| := mul_lt_mul_of_pos_right (by linarith [h₄]) hpos
      linarith [h1, h2, h3]
  have key2 : |x| ≤ |y| → |z| ≤ |y| → y = 0 := by
    intro hx hz
    by_cases hy : y = 0
    · exact hy
    · exfalso
      have hpos : 0 < |y| := abs_pos.mpr hy
      have h1 : a 4 * |y| = |a 4 * y| := by rw [abs_mul, abs_of_pos h₀.2.1]
      have h2 : |a 4 * y| ≤ (-a 3) * |y| + (-a 5) * |y| := by
        have heq : a 4 * y = -(a 3 * x + a 5 * z) := by linarith [h₈]
        rw [heq, abs_neg]
        calc |a 3 * x + a 5 * z| ≤ |a 3 * x| + |a 5 * z| := abs_add_le _ _
          _ = (-a 3) * |x| + (-a 5) * |z| := by
              rw [abs_mul, abs_mul, abs_of_neg h₂.1, abs_of_neg h₂.2]
          _ ≤ (-a 3) * |y| + (-a 5) * |y| := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hx (by linarith [h₂.1])
              · exact mul_le_mul_of_nonneg_left hz (by linarith [h₂.2])
      have h3 : (-a 3) * |y| + (-a 5) * |y| < a 4 * |y| := by
        calc (-a 3) * |y| + (-a 5) * |y| = ((-a 3) + (-a 5)) * |y| := by ring
          _ < a 4 * |y| := mul_lt_mul_of_pos_right (by linarith [h₅]) hpos
      linarith [h1, h2, h3]
  have key3 : |x| ≤ |z| → |y| ≤ |z| → z = 0 := by
    intro hx hy
    by_cases hz : z = 0
    · exact hz
    · exfalso
      have hpos : 0 < |z| := abs_pos.mpr hz
      have h1 : a 8 * |z| = |a 8 * z| := by rw [abs_mul, abs_of_pos h₀.2.2]
      have h2 : |a 8 * z| ≤ (-a 6) * |z| + (-a 7) * |z| := by
        have heq : a 8 * z = -(a 6 * x + a 7 * y) := by linarith [h₉]
        rw [heq, abs_neg]
        calc |a 6 * x + a 7 * y| ≤ |a 6 * x| + |a 7 * y| := abs_add_le _ _
          _ = (-a 6) * |x| + (-a 7) * |y| := by
              rw [abs_mul, abs_mul, abs_of_neg h₃.1, abs_of_neg h₃.2]
          _ ≤ (-a 6) * |z| + (-a 7) * |z| := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hx (by linarith [h₃.1])
              · exact mul_le_mul_of_nonneg_left hy (by linarith [h₃.2])
      have h3 : (-a 6) * |z| + (-a 7) * |z| < a 8 * |z| := by
        calc (-a 6) * |z| + (-a 7) * |z| = ((-a 6) + (-a 7)) * |z| := by ring
          _ < a 8 * |z| := mul_lt_mul_of_pos_right (by linarith [h₆]) hpos
      linarith [h1, h2, h3]
  rcases le_total |x| |y| with hxy | hyx
  · rcases le_total |y| |z| with hyz | hzy
    · have hz0 : z = 0 := key3 (le_trans hxy hyz) hyz
      have hzabs : |z| = 0 := by rw [hz0]; simp
      have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm (le_trans (le_trans hxy hyz) (le_of_eq hzabs)) (abs_nonneg x))
      have hy0 : y = 0 := abs_eq_zero.mp (le_antisymm (le_trans hyz (le_of_eq hzabs)) (abs_nonneg y))
      exact ⟨hx0, hy0, hz0⟩
    · have hy0 : y = 0 := key2 hxy hzy
      have hyabs : |y| = 0 := by rw [hy0]; simp
      have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm (le_trans hxy (le_of_eq hyabs)) (abs_nonneg x))
      have hz0 : z = 0 := abs_eq_zero.mp (le_antisymm (le_trans hzy (le_of_eq hyabs)) (abs_nonneg z))
      exact ⟨hx0, hy0, hz0⟩
  · rcases le_total |x| |z| with hxz | hzx
    · have hz0 : z = 0 := key3 hxz (le_trans hyx hxz)
      have hzabs : |z| = 0 := by rw [hz0]; simp
      have hx0 : x = 0 := abs_eq_zero.mp (le_antisymm (le_trans hxz (le_of_eq hzabs)) (abs_nonneg x))
      have hy0 : y = 0 := abs_eq_zero.mp (le_antisymm (le_trans (le_trans hyx hxz) (le_of_eq hzabs)) (abs_nonneg y))
      exact ⟨hx0, hy0, hz0⟩
    · have hx0 : x = 0 := key1 hyx hzx
      have hxabs : |x| = 0 := by rw [hx0]; simp
      have hy0 : y = 0 := abs_eq_zero.mp (le_antisymm (le_trans hyx (le_of_eq hxabs)) (abs_nonneg y))
      have hz0 : z = 0 := abs_eq_zero.mp (le_antisymm (le_trans hzx (le_of_eq hxabs)) (abs_nonneg z))
      exact ⟨hx0, hy0, hz0⟩
