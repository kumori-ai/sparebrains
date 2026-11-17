import Mathlib

open scoped Nat
open scoped Real

/--
Let $x$, $y$, and $z$ all exceed 1 and let $w$ be a positive number such that \[\log_x w = 24,\quad \log_y w = 40 \quad\text{and}\quad \log_{xyz} w = 12.\]  Find $\log_z w$. -/
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast ht.1
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast ht.2.1
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast ht.2.2

  have hxpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hypos : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hzpos : 0 < Real.log (z : ℝ) := Real.log_pos hz1

  have hxne : Real.log (x : ℝ) ≠ 0 := ne_of_gt hxpos
  have hyne : Real.log (y : ℝ) ≠ 0 := ne_of_gt hypos
  have hzne : Real.log (z : ℝ) ≠ 0 := ne_of_gt hzpos

  have hwx : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    rw [div_eq_iff hxne] at h0
    exact h0
  have hwy : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    rw [div_eq_iff hyne] at h1
    exact h1

  have hx0 : (x : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (x : ℝ) := by linarith
    exact ne_of_gt this
  have hy0 : (y : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (y : ℝ) := by linarith
    exact ne_of_gt this
  have hz0 : (z : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (z : ℝ) := by linarith
    exact ne_of_gt this

  have hlogxyz : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) =
      Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    calc
      Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ))
          = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
              rw [Real.log_mul (mul_ne_zero hx0 hy0) hz0]
      _ = (Real.log (x : ℝ) + Real.log (y : ℝ)) + Real.log (z : ℝ) := by
              rw [Real.log_mul hx0 hy0]
      _ = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
              ring

  have hden_pos : 0 < Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    rw [hlogxyz]
    linarith
  have hden_ne : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) ≠ 0 := ne_of_gt hden_pos

  have h2eq : Real.log (w : ℝ) = 12 * Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    rw [div_eq_iff hden_ne] at h2
    exact h2

  have h2sum : Real.log (w : ℝ) =
      12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    rw [hlogxyz] at h2eq
    exact h2eq

  have hLw_eq : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    nlinarith [hwx, hwy, h2sum]

  rw [hLw_eq]
  field_simp [hzne] <;> ring
