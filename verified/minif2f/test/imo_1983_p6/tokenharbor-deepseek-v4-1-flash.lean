import Mathlib

open scoped Nat
open scoped Real

/-- Let $ a$, $ b$ and $ c$ be the lengths of the sides of a triangle. Prove that
\[ a^{2}b(a -{} b) +{} b^{2}c(b -{} c) +{} c^{2}a(c -{} a)\ge 0.
\]
Determine when equality occurs. -/
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  let x : ℝ := (b + c - a) / 2
  let y : ℝ := (c + a - b) / 2
  let z : ℝ := (a + b - c) / 2
  have hx : 0 < x := by
    dsimp [x]
    linarith
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hz : 0 < z := by
    dsimp [z]
    linarith
  have ha : a = y + z := by
    dsimp [y, z]
    ring
  have hb : b = z + x := by
    dsimp [z, x]
    ring
  have hc : c = x + y := by
    dsimp [x, y]
    ring
  have hE : a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a)
      = 2 * (x * y * (y - z) ^ 2 + y * z * (z - x) ^ 2 + z * x * (x - y) ^ 2) := by
    rw [ha, hb, hc]
    ring
  rw [hE]
  have h1' : 0 ≤ x * y * (y - z) ^ 2 := by
    exact mul_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg (y - z))
  have h2' : 0 ≤ y * z * (z - x) ^ 2 := by
    exact mul_nonneg (mul_nonneg hy.le hz.le) (sq_nonneg (z - x))
  have h3' : 0 ≤ z * x * (x - y) ^ 2 := by
    exact mul_nonneg (mul_nonneg hz.le hx.le) (sq_nonneg (x - y))
  nlinarith [h1', h2', h3']
