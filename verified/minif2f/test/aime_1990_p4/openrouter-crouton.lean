import Mathlib

open scoped Nat
open scoped Real

/--
Find the positive solution to \[ \frac 1{x^2-10x-29}+\frac1{x^2-10x-45}-\frac 2{x^2-10x-69}=0 \] -/
theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by
  have e1 : (1 / (x ^ 2 - 10 * x - 29)) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69)) = (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) := by
    rw [one_div, mul_assoc, ← mul_assoc, inv_mul_cancel₀ h₁, one_mul]
  have e2 : (1 / (x ^ 2 - 10 * x - 45)) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69)) = (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) := by
    rw [one_div, show (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) = (x ^ 2 - 10 * x - 45) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69)) by ring, ← mul_assoc, inv_mul_cancel₀ h₂, one_mul]
  have e3 : (2 / (x ^ 2 - 10 * x - 69)) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69)) = 2 * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)) := by
    rw [div_eq_mul_inv, show (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) = (x ^ 2 - 10 * x - 69) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)) by ring, mul_assoc, ← mul_assoc (x ^ 2 - 10 * x - 69)⁻¹ (x ^ 2 - 10 * x - 69) ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)), inv_mul_cancel₀ h₃, one_mul]
  have hexp : (1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69)) * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69)) = (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) + (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) - 2 * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)) := by
    rw [sub_mul, add_mul, e1, e2, e3]
  have key : (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) + (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) - 2 * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)) = 0 := by
    rw [← hexp, h₄, zero_mul]
  have hid : (x ^ 2 - 10 * x - 45) * (x ^ 2 - 10 * x - 69) + (x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 69) - 2 * ((x ^ 2 - 10 * x - 29) * (x ^ 2 - 10 * x - 45)) = -64 * (x ^ 2 - 10 * x - 39) := by ring
  rw [hid] at key
  have ht : x ^ 2 - 10 * x = 39 := by linarith
  have hfact : (x - 13) * (x + 3) = 0 := by
    have h : (x - 13) * (x + 3) = x ^ 2 - 10 * x - 39 := by ring
    rw [h]
    linarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith
