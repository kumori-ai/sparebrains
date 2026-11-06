import Mathlib

open scoped Nat
open scoped Real

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  rcases h₀ with ⟨hx, ⟨hy, hz⟩⟩
  have hS : 0 < x + y + z := by linarith
  have hxy : 0 < x + y := by linarith
  have hyz : 0 < y + z := by linarith
  have hzx : 0 < z + x := by linarith
  have hS_ne : x + y + z ≠ 0 := ne_of_gt hS
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy
  have hyz_ne : y + z ≠ 0 := ne_of_gt hyz
  have hzx_ne : z + x ≠ 0 := ne_of_gt hzx
  field_simp [hS_ne, hxy_ne, hyz_ne, hzx_ne]
  ring_nf
  have hxy_nonneg : 0 ≤ x + y := by linarith
  have hsq1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  have h1 : 0 ≤ (x + y) * (x - y)^2 := mul_nonneg hxy_nonneg hsq1
  have hyz_nonneg : 0 ≤ y + z := by linarith
  have hsq2 : 0 ≤ (y - z)^2 := sq_nonneg (y - z)
  have h2 : 0 ≤ (y + z) * (y - z)^2 := mul_nonneg hyz_nonneg hsq2
  have hzx_nonneg : 0 ≤ z + x := by linarith
  have hsq3 : 0 ≤ (z - x)^2 := sq_nonneg (z - x)
  have h3 : 0 ≤ (z + x) * (z - x)^2 := mul_nonneg hzx_nonneg hsq3
  nlinarith
