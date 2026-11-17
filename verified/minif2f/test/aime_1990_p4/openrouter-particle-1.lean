import Mathlib

open scoped Nat
open scoped Real

/--
Find the positive solution to \[ \frac 1{x^2-10x-29}+\frac1{x^2-10x-45}-\frac 2{x^2-10x-69}=0 \] -/
theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by
  set A : ℝ := x ^ 2 - 10 * x - 29 with hAdef
  set B : ℝ := x ^ 2 - 10 * x - 45 with hBdef
  set C : ℝ := x ^ 2 - 10 * x - 69 with hCdef
  have hA : A ≠ 0 := by simpa [hAdef] using h₁
  have hB : B ≠ 0 := by simpa [hBdef] using h₂
  have hC : C ≠ 0 := by simpa [hCdef] using h₃
  have h : 1 / A + 1 / B - 2 / C = 0 := by
    simpa [hAdef, hBdef, hCdef] using h₄
  have h1 : (A * B * C) * (1 / A) = B * C := by
    field_simp [hA] <;> ring
  have h2 : (A * B * C) * (1 / B) = A * C := by
    field_simp [hB] <;> ring
  have h3 : (A * B * C) * (2 / C) = 2 * A * B := by
    field_simp [hC] <;> ring
  have hpoly : B * C + A * C - 2 * A * B = 0 := by
    calc
      B * C + A * C - 2 * A * B = (A * B * C) * (1 / A) + (A * B * C) * (1 / B) - (A * B * C) * (2 / C) := by rw [h1, h2, h3] <;> ring
      _ = (A * B * C) * (1 / A + 1 / B - 2 / C) := by ring
      _ = (A * B * C) * 0 := by rw [h]
      _ = 0 := by ring
  have hpoly' : x ^ 2 - 10 * x - 39 = 0 := by
    have hEq : B * C + A * C - 2 * A * B = -64 * (x ^ 2 - 10 * x - 39) := by
      rw [hAdef, hBdef, hCdef]
      ring
    rw [hEq] at hpoly
    nlinarith
  have hfac : (x - 13) * (x + 3) = 0 := by
    calc
      (x - 13) * (x + 3) = x ^ 2 - 10 * x - 39 := by ring
      _ = 0 := hpoly'
  have hx3pos : 0 < x + 3 := by linarith
  have hx3 : x + 3 ≠ 0 := ne_of_gt hx3pos
  have hx13 : x - 13 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact h
    · exact False.elim (hx3 h)
  linarith
