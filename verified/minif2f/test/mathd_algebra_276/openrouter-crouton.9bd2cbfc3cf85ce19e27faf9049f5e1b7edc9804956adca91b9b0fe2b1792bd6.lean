import Mathlib

open scoped Nat
open scoped Real

/--
The expression $10x^2-x-24$ can be written as $(Ax-8)(Bx+3),$ where $A$ and $B$ are integers. What is $AB + B$? -/
theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by
  have h1 := h₀ 1
  have hm1 := h₀ (-1)
  ring_nf at h1 hm1
  have habR : (a : ℝ) * (b : ℝ) = 10 := by linarith
  have hlinR : 3 * (a : ℝ) - 8 * (b : ℝ) = -1 := by linarith
  have h3a : 3 * (a : ℝ) = 8 * (b : ℝ) - 1 := by linarith
  have hb_eq : (b : ℝ) * (8 * (b : ℝ) - 1) = 30 := by
    have h : (b : ℝ) * (3 * (a : ℝ)) = 30 := by
      have h' : (b : ℝ) * (3 * (a : ℝ)) = 3 * ((a : ℝ) * (b : ℝ)) := by ring
      rw [h', habR]; norm_num
    rwa [h3a] at h
  have hfactor : ((b : ℝ) - 2) * (8 * (b : ℝ) + 15) = 0 := by
    have h : ((b : ℝ) - 2) * (8 * (b : ℝ) + 15)
        = (b : ℝ) * (8 * (b : ℝ) - 1) - 30 := by ring
    rw [h, hb_eq]; norm_num
  have habZ : a * b = 10 := by exact_mod_cast habR
  rcases mul_eq_zero.mp hfactor with hb | hb
  · have hbZ : b = 2 := by
      have h : (b : ℝ) = 2 := by linarith
      exact_mod_cast h
    rw [hbZ] at habZ ⊢
    omega
  · have hbZ : 8 * b + 15 = 0 := by
      have h : 8 * (b : ℝ) + 15 = 0 := by linarith
      exact_mod_cast h
    omega
