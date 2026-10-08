import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha : a ^ 2 + a = 1 := by
    rw [h₀, add_comm] at h₁
    exact h₁
  have hc : c ^ 2 + c = 1 := by
    rw [h₂, add_comm] at h₃
    exact h₃
  have hdiff : (a - c) * (a + c + 1) = 0 := by
    have : a ^ 2 + a - (c ^ 2 + c) = 0 := by
      rw [ha, hc]
      ring
    rw [sub_eq_zero] at this
    rw [pow_two, pow_two] at this
    ring_nf at this
    linarith
  have hac : a + c + 1 = 0 := by
    by_contra h
    push_neg at h
    have : (a - c) = 0 := by
      aesop
    apply h₄
    rw [sub_eq_zero] at this
    exact this
  have hsum : a + c = -1 := by
    linarith
  have hprod : a * c = -1 := by
    have : a ^ 2 + a = 1 := ha
    have : c ^ 2 + c = 1 := hc
    have : a ^ 2 + a + c ^ 2 + c = 2 := by
      linarith
    have : (a + c) ^ 2 - 2 * a * c + (a + c) = 2 := by
      ring_nf
      linarith
    nlinarith
  have hdist_sq : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    rw [h₀, h₂]
    ring_nf
    nlinarith
  rw [hdist_sq]