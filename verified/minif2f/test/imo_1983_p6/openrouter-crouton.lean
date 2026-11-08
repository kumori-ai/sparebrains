import Mathlib

open scoped Nat
open scoped Real

/-- Let $ a$, $ b$ and $ c$ be the lengths of the sides of a triangle. Prove that
\[ a^{2}b(a -{} b) +{} b^{2}c(b -{} c) +{} c^{2}a(c -{} a)\ge 0.
\]
Determine when equality occurs. -/
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  obtain ⟨ha, hb, hc⟩ := h₀
  set x := (b + c - a) / 2 with hx_def
  set y := (c + a - b) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  have hx : 0 < x := by
    rw [hx_def]
    linarith
  have hy : 0 < y := by
    rw [hy_def]
    linarith
  have hz : 0 < z := by
    rw [hz_def]
    linarith
  have h_id : a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a)
      = 2 * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z)) := by
    rw [hx_def, hy_def, hz_def]
    ring
  rw [h_id]
  have h1 : 0 ≤ x * y * (y - z) ^ 2 :=
    mul_nonneg (mul_nonneg hx.le hy.le) (sq_nonneg _)
  have h2 : 0 ≤ y * z * (z - x) ^ 2 :=
    mul_nonneg (mul_nonneg hy.le hz.le) (sq_nonneg _)
  have h3 : 0 ≤ z * x * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg hz.le hx.le) (sq_nonneg _)
  have h4 : x * y * (y - z) ^ 2 + y * z * (z - x) ^ 2 + z * x * (x - y) ^ 2
      = x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z) := by
    ring
  have h_nonneg : 0 ≤ x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z) := by
    rw [← h4]
    exact add_nonneg (add_nonneg h1 h2) h3
  linarith
