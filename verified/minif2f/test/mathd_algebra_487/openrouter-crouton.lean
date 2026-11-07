import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha : a ^ 2 + a = 1 := by linarith
  have hc : c ^ 2 + c = 1 := by linarith
  have hsum : a + c = -1 := by
    have hfactor : (a - c) * (a + c + 1) = 0 := by
      have h : a ^ 2 + a = c ^ 2 + c := by linarith
      calc (a - c) * (a + c + 1) = (a ^ 2 + a) - (c ^ 2 + c) := by ring
        _ = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with h | h
    · exfalso
      apply h₄
      linarith
    · linarith
  have hprod : a * c = -1 := by
    have h1 : (a + c) ^ 2 = a ^ 2 + c ^ 2 + 2 * (a * c) := by ring
    have ha2 : a ^ 2 = 1 - a := by linarith
    have hc2 : c ^ 2 = 1 - c := by linarith
    have h2 : (1 : ℝ) = (1 - a) + (1 - c) + 2 * (a * c) := by
      calc (1 : ℝ) = (a + c) ^ 2 := by rw [hsum]; norm_num
        _ = a ^ 2 + c ^ 2 + 2 * (a * c) := h1
        _ = (1 - a) + (1 - c) + 2 * (a * c) := by rw [ha2, hc2]
    linarith
  have hsq : (a - c) ^ 2 = 5 := by
    calc (a - c) ^ 2 = (a + c) ^ 2 - 4 * (a * c) := by ring
      _ = (-1) ^ 2 - 4 * (-1) := by rw [hsum, hprod]
      _ = 5 := by norm_num
  have hb : b - d = -(a - c) := by
    have h1 : b - d = a ^ 2 - c ^ 2 := by rw [h₀, h₂]
    have h2 : a ^ 2 - c ^ 2 = (a - c) * (a + c) := by ring
    rw [h1, h2, hsum]; ring
  have hdist : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    rw [hb]
    have h3 : (-(a - c)) ^ 2 = (a - c) ^ 2 := by ring
    rw [h3, hsq]; norm_num
  rw [hdist]
