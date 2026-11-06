import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha_eq : a ^ 2 + a - 1 = 0 := by
    linarith [h₀, h₁]
  have hc_eq : c ^ 2 + c - 1 = 0 := by
    linarith [h₂, h₃]
  have hsum : a + c = -1 := by
    have hsub : (a ^ 2 + a - 1) - (c ^ 2 + c - 1) = 0 := by rw [ha_eq, hc_eq, sub_self]
    have factor : (a ^ 2 + a - 1) - (c ^ 2 + c - 1) = (a - c) * (a + c + 1) := by ring
    rw [factor] at hsub
    have hzero : (a - c) * (a + c + 1) = 0 := hsub
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
    · exfalso; exact h₄ (sub_eq_zero.mp h)
    · linarith
  have hprod : a * c = -1 := by
    have hsq : (a + c) ^ 2 = a ^ 2 + c ^ 2 + 2 * (a * c) := by ring
    have ha_sq : a ^ 2 = 1 - a := by linarith
    have hc_sq : c ^ 2 = 1 - c := by linarith
    rw [ha_sq, hc_sq] at hsq
    rw [hsum] at hsq
    nlinarith
  have h_diff_sq : (a - c) ^ 2 = 5 := by
    calc
      (a - c) ^ 2 = (a + c) ^ 2 - 4 * (a * c) := by ring
      _ = (-1) ^ 2 - 4 * (-1) := by rw [hsum, hprod]
      _ = 5 := by ring
  have h_bd_sq : (b - d) ^ 2 = (a - c) ^ 2 := by
    calc
      (b - d) ^ 2 = (a ^ 2 - c ^ 2) ^ 2 := by rw [h₀, h₂]
      _ = ((a - c) * (a + c)) ^ 2 := by ring
      _ = (a - c) ^ 2 * (a + c) ^ 2 := by ring
      _ = (a - c) ^ 2 * ((-1) ^ 2) := by rw [hsum]
      _ = (a - c) ^ 2 * 1 := by ring
      _ = (a - c) ^ 2 := by ring
  have h_total : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    rw [h_bd_sq, h_diff_sq]
    ring
  rw [h_total]
