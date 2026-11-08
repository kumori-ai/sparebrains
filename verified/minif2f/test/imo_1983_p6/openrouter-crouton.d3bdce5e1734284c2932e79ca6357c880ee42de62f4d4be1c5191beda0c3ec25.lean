import Mathlib

open scoped Nat
open scoped Real

/-- Let $ a$, $ b$ and $ c$ be the lengths of the sides of a triangle. Prove that
\[ a^{2}b(a -{} b) +{} b^{2}c(b -{} c) +{} c^{2}a(c -{} a)\ge 0.
\]
Determine when equality occurs. -/
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have hx : 0 < (b + c - a) / 2 := by linarith
  have hy : 0 < (c + a - b) / 2 := by linarith
  have hz : 0 < (a + b - c) / 2 := by linarith
  have key : a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a)
      = 2 * (((b + c - a) / 2) * ((a + b - c) / 2) * (((b + c - a) / 2) - ((c + a - b) / 2)) ^ 2
          + ((b + c - a) / 2) * ((c + a - b) / 2) * (((c + a - b) / 2) - ((a + b - c) / 2)) ^ 2
          + ((c + a - b) / 2) * ((a + b - c) / 2) * (((a + b - c) / 2) - ((b + c - a) / 2)) ^ 2) := by
    ring
  rw [key]
  have t1 : 0 ≤ ((b + c - a) / 2) * ((a + b - c) / 2) * (((b + c - a) / 2) - ((c + a - b) / 2)) ^ 2 :=
    mul_nonneg (mul_nonneg hx.le hz.le) (sq_nonneg _)
  have t2 : 0 ≤ ((b + c - a) / 2) * ((c + a - b) / 2) * (((c + a - b) / 2) - ((a + b - c) / 2)) ^ 2 :=
    mul_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg _)
  have t3 : 0 ≤ ((c + a - b) / 2) * ((a + b - c) / 2) * (((a + b - c) / 2) - ((b + c - a) / 2)) ^ 2 :=
    mul_nonneg (mul_nonneg hy.le hz.le) (sq_nonneg _)
  linarith
