import Mathlib

open scoped Nat
open scoped Real

/-- Let $ a$, $ b$ and $ c$ be the lengths of the sides of a triangle. Prove that
\[ a^{2}b(a -{} b) +{} b^{2}c(b -{} c) +{} c^{2}a(c -{} a)\ge 0.
\]
Determine when equality occurs. -/
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  rcases h₀ with ⟨ha, hb, hc⟩
  set x := (b + c - a) / 2 with hxdef
  set y := (c + a - b) / 2 with hydef
  set z := (a + b - c) / 2 with hzdef
  have hxpos : 0 < x := by
    rw [hxdef]
    linarith
  have hypos : 0 < y := by
    rw [hydef]
    linarith
  have hzpos : 0 < z := by
    rw [hzdef]
    linarith
  have ha_eq : a = y + z := by linarith
  have hb_eq : b = z + x := by linarith
  have hc_eq : c = x + y := by linarith
  have hE : a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) =
      2 * (x * z * (x - y) ^ 2 + y * x * (y - z) ^ 2 + z * y * (z - x) ^ 2) := by
    rw [ha_eq, hb_eq, hc_eq]
    ring
  rw [hE]
  have hx' : 0 ≤ x := le_of_lt hxpos
  have hy' : 0 ≤ y := le_of_lt hypos
  have hz' : 0 ≤ z := le_of_lt hzpos
  have h1 : 0 ≤ x * z * (x - y) ^ 2 := by
    apply mul_nonneg (mul_nonneg hx' hz') (pow_two_nonneg _)
  have h2 : 0 ≤ y * x * (y - z) ^ 2 := by
    apply mul_nonneg (mul_nonneg hy' hx') (pow_two_nonneg _)
  have h3 : 0 ≤ z * y * (z - x) ^ 2 := by
    apply mul_nonneg (mul_nonneg hz' hy') (pow_two_nonneg _)
  have hsum : 0 ≤ x * z * (x - y) ^ 2 + y * x * (y - z) ^ 2 + z * y * (z - x) ^ 2 := by
    linarith
  have two_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  exact mul_nonneg two_nonneg hsum
