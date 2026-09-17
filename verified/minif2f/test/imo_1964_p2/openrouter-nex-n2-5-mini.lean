import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have hx : 0 < (b + c - a) / 2 := by linarith
  have hy : 0 < (a + c - b) / 2 := by linarith
  have hz : 0 < (a + b - c) / 2 := by linarith
  let x : ℝ := (b + c - a) / 2
  let y : ℝ := (a + c - b) / 2
  let z : ℝ := (a + b - c) / 2
  have hxyz : 0 < x ∧ 0 < y ∧ 0 < z := ⟨hx, hy, hz⟩
  have ha : a = y + z := by ring
  have hb : b = x + z := by ring
  have hc : c = x + y := by ring
  simp only [ha, hb, hc]
  have hdiff :
      x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2 =
        3 * (x + y) * (x + z) * (y + z) -
          ((y + z) ^ 2 * (2 * x) + (x + z) ^ 2 * (2 * y) + (x + y) ^ 2 * (2 * z)) := by
    ring
  have hnonneg :
      0 ≤ x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2 := by
    positivity
  linarith [hdiff, hnonneg]
