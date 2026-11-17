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
    linarith [h₃]
  have hy : 0 < y := by
    dsimp [y]
    linarith [h₂]
  have hz : 0 < z := by
    dsimp [z]
    linarith [h₁]
  have ha : a = y + z := by
    dsimp [y, z]
    ring
  have hb : b = z + x := by
    dsimp [z, x]
    ring
  have hc : c = x + y := by
    dsimp [x, y]
    ring
  have hE :
      a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a)
        = 2 * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z)) := by
    rw [ha, hb, hc]
    ring
  rw [hE]
  have hF : 0 ≤ x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z) := by
    have hden : 0 < x + y + z := by
      linarith [hx, hy, hz]
    have hnum :
        0 ≤ y * (x * y - z ^ 2) ^ 2 + x * (y ^ 2 - x * z) ^ 2 +
          z * (z * y - x ^ 2) ^ 2 := by
      have h1 : 0 ≤ y * (x * y - z ^ 2) ^ 2 :=
        mul_nonneg (le_of_lt hy) (sq_nonneg _)
      have h2 : 0 ≤ x * (y ^ 2 - x * z) ^ 2 :=
        mul_nonneg (le_of_lt hx) (sq_nonneg _)
      have h3 : 0 ≤ z * (z * y - x ^ 2) ^ 2 :=
        mul_nonneg (le_of_lt hz) (sq_nonneg _)
      linarith
    have hident :
        x * y ^ 3 + y * z ^ 3 + z * x ^ 3 - x * y * z * (x + y + z)
          = (y * (x * y - z ^ 2) ^ 2 + x * (y ^ 2 - x * z) ^ 2 +
              z * (z * y - x ^ 2) ^ 2) / (x + y + z) := by
      field_simp [ne_of_gt hden]
      ring
    rw [hident]
    exact div_nonneg hnum (le_of_lt hden)
  nlinarith
