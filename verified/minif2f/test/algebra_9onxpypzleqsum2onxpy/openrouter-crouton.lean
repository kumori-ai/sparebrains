import Mathlib

open scoped Nat
open scoped Real

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  obtain ⟨hx, hy, hz⟩ := h₀
  have hxy : 0 < x + y := add_pos hx hy
  have hyz : 0 < y + z := add_pos hy hz
  have hzx : 0 < z + x := add_pos hz hx
  have hS : 0 < x + y + z := add_pos hxy hz
  have hden : 0 < (x + y) * (y + z) * (z + x) := mul_pos (mul_pos hxy hyz) hzx
  have key : 9 * ((x + y) * (y + z) * (z + x))
      ≤ 2 * (x + y + z) * ((y + z) * (z + x) + (z + x) * (x + y) + (x + y) * (y + z)) := by
    nlinarith [mul_nonneg (sq_nonneg (x - y)) (le_of_lt hxy),
      mul_nonneg (sq_nonneg (y - z)) (le_of_lt hyz),
      mul_nonneg (sq_nonneg (z - x)) (le_of_lt hzx)]
  have hRHS : 2 / (x + y) + 2 / (y + z) + 2 / (z + x)
      = 2 * ((y + z) * (z + x) + (z + x) * (x + y) + (x + y) * (y + z))
        / ((x + y) * (y + z) * (z + x)) := by
    field_simp
  rw [hRHS, div_le_iff₀ hS, div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [key]
