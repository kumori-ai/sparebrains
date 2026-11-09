import Mathlib

open scoped Nat
open scoped Real

/--
If $ x$, $ y$, and $ z$ are positive numbers satisfying \[x +{} 1/y ={} 4,\quad  y +{} 1/z ={} 1,\quad\text{and}\quad z +{} 1/x ={} 7/3,\] then $ xyz ={}$

$ \textbf{(A)}\ 2/3 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 4/3 \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 7/3$ -/
theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  obtain ⟨hx, hy, hz⟩ := h₀
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  have hzne : z ≠ 0 := ne_of_gt hz
  have hxy : x * y + 1 = 4 * y := by
    calc x * y + 1 = (x + 1 / y) * y := by rw [add_mul, one_div_mul_cancel hyne]
      _ = 4 * y := by rw [h₁]
  have hyz : y * z + 1 = z := by
    calc y * z + 1 = (y + 1 / z) * z := by rw [add_mul, one_div_mul_cancel hzne]
      _ = 1 * z := by rw [h₂]
      _ = z := by ring
  have hzx : z * x + 1 = 7 / 3 * x := by
    calc z * x + 1 = (z + 1 / x) * x := by rw [add_mul, one_div_mul_cancel hxne]
      _ = 7 / 3 * x := by rw [h₃]
  have h1z : x * y * z + z = 4 * (y * z) := by linear_combination z * hxy
  have h2x : x * y * z + x = z * x := by linear_combination x * hyz
  have h3y : x * y * z + y = 7 / 3 * (x * y) := by linear_combination y * hzx
  have hpz : x * y * z = 3 * z - 4 := by linarith
  have hpx : x * y * z = 4 / 3 * x - 1 := by linarith
  have hpy : x * y * z = 25 / 3 * y - 7 / 3 := by linarith
  set p := x * y * z with hp_def
  have hp_pos : 0 < p := by
    rw [hp_def]
    exact mul_pos (mul_pos hx hy) hz
  have hx_eq : x = 3 * (p + 1) / 4 := by linarith
  have hy_eq : y = (3 * p + 7) / 25 := by linarith
  have hz_eq : z = (p + 4) / 3 := by linarith
  have hpoly : 100 * p = (p + 1) * (3 * p + 7) * (p + 4) := by
    calc 100 * p = 100 * (x * y * z) := by rw [hp_def]
      _ = 100 * ((3 * (p + 1) / 4) * ((3 * p + 7) / 25) * ((p + 4) / 3)) := by
          rw [hx_eq, hy_eq, hz_eq]
      _ = (p + 1) * (3 * p + 7) * (p + 4) := by ring
  have hfact : (p - 1) ^ 2 * (3 * p + 28) = 0 := by linear_combination -hpoly
  rcases mul_eq_zero.mp hfact with h | h
  · have hp1 : p - 1 = 0 := by
      have h' : (p - 1) * (p - 1) = 0 := by
        have hh := h
        rw [pow_two] at hh
        exact hh
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact h1
      · exact h1
    linarith
  · linarith
