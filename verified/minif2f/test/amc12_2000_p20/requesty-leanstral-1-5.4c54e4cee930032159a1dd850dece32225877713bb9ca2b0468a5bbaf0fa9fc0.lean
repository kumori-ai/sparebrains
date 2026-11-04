import Mathlib

open scoped Nat
open scoped Real

/--
If $ x$, $ y$, and $ z$ are positive numbers satisfying \[x +{} 1/y ={} 4,\quad  y +{} 1/z ={} 1,\quad\text{and}\quad z +{} 1/x ={} 7/3,\] then $ xyz ={}$

$ \textbf{(A)}\ 2/3 \qquad \textbf{(B)}\ 1 \qquad \textbf{(C)}\ 4/3 \qquad \textbf{(D)}\ 2 \qquad \textbf{(E)}\ 7/3$ -/
theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by
  rcases h₀ with ⟨hx, hy, hz⟩
  have hx_ne : x ≠ 0 := by linarith
  have hy_ne : y ≠ 0 := by linarith
  have hz_ne : z ≠ 0 := by linarith
  have ht_ne : x * y * z ≠ 0 := mul_ne_zero (mul_ne_zero hx_ne hy_ne) hz_ne
  set t := x * y * z with ht
  have h_sum : (x + 1 / y) + (y + 1 / z) + (z + 1 / x) = 22/3 := by
    rw [h₁, h₂, h₃]
    ring
  have h_prod : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = 28/3 := by
    rw [h₁, h₂, h₃]
    ring
  have expand_eq : (x + 1 / y) * (y + 1 / z) * (z + 1 / x) = t + ((x + y + z) + (1 / x + 1 / y + 1 / z)) + 1 / t := by
    field_simp [hx_ne, hy_ne, hz_ne, ht_ne]
    ring
  have h_sum_eq : (x + y + z) + (1 / x + 1 / y + 1 / z) = 22/3 := by
    calc
      (x + y + z) + (1 / x + 1 / y + 1 / z) = (x + 1 / y) + (y + 1 / z) + (z + 1 / x) := by abel
      _ = 22/3 := h_sum
  have h_eq : t + ((x + y + z) + (1 / x + 1 / y + 1 / z)) + 1 / t = 28/3 := by
    rw [← expand_eq, h_prod]
  rw [h_sum_eq] at h_eq
  have h_t_eq : t + 1 / t = 2 := by
    linarith
  field_simp [ht_ne] at h_t_eq
  nlinarith
