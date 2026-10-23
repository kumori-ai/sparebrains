import Mathlib

open scoped Nat
open scoped Real

/--
If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? -/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h_y : y = (2 : ℝ) / 5 * x := by
    have h_y1 : 5 * y = 2 * x := by linarith
    have h_y2 : y = (2 : ℝ) / 5 * x := by
      field_simp [h₀] at h_y1 ⊢
      ring_nf at h_y1 ⊢
      linarith
    exact h_y2
  have h_z : z = 7 / 25 * x := by
    have h_z1 : 10 * z = 7 * y := by linarith
    have h_z2 : z = 7 / 25 * x := by
      calc
        z = (7 * y) / 10 := by
          field_simp
          ring_nf
          <;> linarith
        _ = (7 * ((2 : ℝ) / 5 * x)) / 10 := by rw [h_y]
        _ = 7 / 25 * x := by
          ring_nf
          <;> field_simp
          <;> ring_nf
    exact h_z2
  have h_div : z / x = 7 / 25 := by
    calc
      z / x = (7 / 25 * x) / x := by rw [h_z]
      _ = 7 / 25 := by
        field_simp [h₀]
  exact h_div
