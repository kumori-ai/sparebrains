import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have hx : 0 < b + c - a := by linarith
  have hy : 0 < c + a - b := by linarith
  have hz : 0 < a + b - c := by linarith
  have h1 : 0 ≤ (a + b - c) * ((b + c - a) - (c + a - b)) ^ 2 :=
    mul_nonneg hz.le (sq_nonneg _)
  have h2 : 0 ≤ (b + c - a) * ((c + a - b) - (a + b - c)) ^ 2 :=
    mul_nonneg hx.le (sq_nonneg _)
  have h3 : 0 ≤ (c + a - b) * ((a + b - c) - (b + c - a)) ^ 2 :=
    mul_nonneg hy.le (sq_nonneg _)
  have hid : 3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c))
      = (1 / 8 : ℝ) * ((a + b - c) * ((b + c - a) - (c + a - b)) ^ 2
        + (b + c - a) * ((c + a - b) - (a + b - c)) ^ 2
        + (c + a - b) * ((a + b - c) - (b + c - a)) ^ 2) := by
    ring
  have hsum : 0 ≤ (1 / 8 : ℝ) * ((a + b - c) * ((b + c - a) - (c + a - b)) ^ 2
      + (b + c - a) * ((c + a - b) - (a + b - c)) ^ 2
      + (c + a - b) * ((a + b - c) - (b + c - a)) ^ 2) :=
    mul_nonneg (by norm_num) (add_nonneg (add_nonneg h1 h2) h3)
  have hdiff : 0 ≤ 3 * a * b * c - (a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c)) := by
    rw [hid]
    exact hsum
  exact sub_nonneg.mp hdiff
