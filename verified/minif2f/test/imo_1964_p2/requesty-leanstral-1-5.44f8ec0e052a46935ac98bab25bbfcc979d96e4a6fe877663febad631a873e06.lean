import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  rcases h₀ with ⟨ha, hb, hc⟩
  set x := b + c - a
  set y := c + a - b
  set z := a + b - c
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hz_pos : 0 < z := by linarith
  have ha_eq : 2 * a = y + z := by linarith
  have hb_eq : 2 * b = z + x := by linarith
  have hc_eq : 2 * c = x + y := by linarith
  have h_main : 2 * (x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2) ≤ 3 * (y + z) * (z + x) * (x + y) := by
    have h_diff : 3 * (y + z) * (z + x) * (x + y) - 2 * (x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2) =
        x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
      ring
    have h_nonneg : 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by
      apply add_nonneg
      · apply add_nonneg
        · apply mul_nonneg hx_pos.le; apply pow_two_nonneg
        · apply mul_nonneg hy_pos.le; apply pow_two_nonneg
      · apply mul_nonneg hz_pos.le; apply pow_two_nonneg
    linarith
  have h_mul : 8 * (a ^ 2 * x + b ^ 2 * y + c ^ 2 * z) = 2 * (x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2) := by
    calc
      8 * (a ^ 2 * x + b ^ 2 * y + c ^ 2 * z) = (8 * a ^ 2 * x) + (8 * b ^ 2 * y) + (8 * c ^ 2 * z) := by ring
      _ = (2 * (2 * a) ^ 2 * x) + (2 * (2 * b) ^ 2 * y) + (2 * (2 * c) ^ 2 * z) := by ring
      _ = (2 * (y + z) ^ 2 * x) + (2 * (z + x) ^ 2 * y) + (2 * (x + y) ^ 2 * z) := by rw [ha_eq, hb_eq, hc_eq]
      _ = 2 * (x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2) := by ring
  have h_mul' : 8 * (3 * a * b * c) = 3 * (y + z) * (z + x) * (x + y) := by
    calc
      8 * (3 * a * b * c) = 3 * (2 * a) * (2 * b) * (2 * c) := by ring
      _ = 3 * (y + z) * (z + x) * (x + y) := by rw [ha_eq, hb_eq, hc_eq]
  have h_mul_ineq : 8 * (a ^ 2 * x + b ^ 2 * y + c ^ 2 * z) ≤ 8 * (3 * a * b * c) := by
    rw [h_mul, h_mul']
    exact h_main
  linarith
