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
  have ha : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hb : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hc : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  have hx_ne : (x : ℝ) ≠ 0 := by linarith
  have hy_ne : (y : ℝ) ≠ 0 := by linarith
  have hz_ne : (z : ℝ) ≠ 0 := by linarith
  have hlogxyz : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ))
      = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    rw [Real.log_mul (mul_ne_zero hx_ne hy_ne) hz_ne, Real.log_mul hx_ne hy_ne]
  have e1 : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := (div_eq_iff ha.ne').mp h0
  have e2 : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := (div_eq_iff hb.ne').mp h1
  have hsum_ne : Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) ≠ 0 := by
    linarith
  have e3 : Real.log (w : ℝ)
      = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    have h2' : Real.log (w : ℝ)
        / (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) = 12 := by
      rwa [hlogxyz] at h2
    exact (div_eq_iff hsum_ne).mp h2'
  have e4 : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    linear_combination (-5 / 2 : ℝ) * e1 + (-3 / 2 : ℝ) * e2 + 5 * e3
  exact (div_eq_iff hc.ne').mpr e4
