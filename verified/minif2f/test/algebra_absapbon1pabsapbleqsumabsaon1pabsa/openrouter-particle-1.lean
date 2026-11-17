import Mathlib

open scoped Nat
open scoped Real

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  set x := abs a with hxdef
  set y := abs b with hydef
  set z := abs (a + b) with hzdef
  have hx : 0 ≤ x := by
    rw [hxdef]
    exact abs_nonneg a
  have hy : 0 ≤ y := by
    rw [hydef]
    exact abs_nonneg b
  have hz : 0 ≤ z := by
    rw [hzdef]
    exact abs_nonneg (a + b)
  have hzle : z ≤ x + y := by
    rw [hzdef, hxdef, hydef]
    exact abs_add_le a b
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hzxy : 0 ≤ z * x * y := by
    exact mul_nonneg (mul_nonneg hz hx) hy
  have hdenz : 0 < 1 + z := by linarith
  have hdenx : 0 < 1 + x := by linarith
  have hdeny : 0 < 1 + y := by linarith
  rw [div_le_iff₀ hdenz]
  field_simp [hdenx.ne', hdeny.ne']
  nlinarith [hzle, hxy, hzxy]
