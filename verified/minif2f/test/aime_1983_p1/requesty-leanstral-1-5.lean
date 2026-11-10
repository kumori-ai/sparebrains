import Mathlib

open scoped Nat
open scoped Real

/--
Let $x$, $y$, and $z$ all exceed 1 and let $w$ be a positive number such that \[\log_x w = 24,\quad \log_y w = 40 \quad\text{and}\quad \log_{xyz} w = 12.\]  Find $\log_z w$. -/
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  rcases ht with ⟨hx, hy, hz⟩
  have hxpos : (x : ℝ) > 1 := by exact_mod_cast hx
  have hypos : (y : ℝ) > 1 := by exact_mod_cast hy
  have hzpos : (z : ℝ) > 1 := by exact_mod_cast hz
  have hxpos_ne : (x : ℝ) ≠ 0 := by linarith
  have hypos_ne : (y : ℝ) ≠ 0 := by linarith
  have hzpos_ne : (z : ℝ) ≠ 0 := by linarith
  have hlogx_ne : Real.log (x : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos hxpos)
  have hlogy_ne : Real.log (y : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos hypos)
  have hlogz_ne : Real.log (z : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos hzpos)
  have hpos : (x : ℝ) * (y : ℝ) * (z : ℝ) > 1 := by
    have hxy : (x : ℝ) * (y : ℝ) > 1 := by nlinarith
    nlinarith
  have hlogxyz_ne : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) ≠ 0 := by
    exact ne_of_gt (Real.log_pos hpos)
  have h0' : Real.log w = 24 * Real.log (x : ℝ) := by
    simpa using (div_eq_iff hlogx_ne).mp h0
  have h1' : Real.log w = 40 * Real.log (y : ℝ) := by
    simpa using (div_eq_iff hlogy_ne).mp h1
  have h2' : Real.log w = 12 * Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    simpa [Nat.cast_mul] using (div_eq_iff hlogxyz_ne).mp h2
  have hlog_mul : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    calc
      Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
        rw [Real.log_mul (mul_ne_zero hxpos_ne hypos_ne) hzpos_ne]
      _ = (Real.log (x : ℝ) + Real.log (y : ℝ)) + Real.log (z : ℝ) := by
        rw [Real.log_mul hxpos_ne hypos_ne]
      _ = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by ring
  rw [hlog_mul] at h2'
  set d := Real.log w with hd
  set a := Real.log (x : ℝ) with ha
  set b := Real.log (y : ℝ) with hb
  set c := Real.log (z : ℝ) with hc
  have h0_eq : d = 24 * a := h0'
  have h1_eq : d = 40 * b := h1'
  have h2_eq : d = 12 * (a + b + c) := h2'
  have hgoal : d = 60 * c := by
    linarith
  rw [hd, hc]
  rw [div_eq_iff hlogz_ne]
  exact hgoal
