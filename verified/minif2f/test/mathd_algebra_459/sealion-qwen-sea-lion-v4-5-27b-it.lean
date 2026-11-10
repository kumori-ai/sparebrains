import Mathlib

open scoped Nat
open scoped Real

/--
Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h_a : a = 1 := by
    have h₁' : 5 * b = 4 * a := by linarith
    have h₂' : 3 * c = 4 * a := by linarith
    have h₃' : 24 * a = 24 := by
      have h₄ : 10 * b = 8 * a := by linarith
      have h₅ : 6 * c = 8 * a := by linarith
      linarith
    linarith
  have h_b : b = 4 / 5 := by
    have h₁' : 5 * b = 4 * a := by linarith
    rw [h_a] at h₁'
    linarith
  have h_c : c = 4 / 3 := by
    have h₂' : 3 * c = 4 * a := by linarith
    rw [h_a] at h₂'
    linarith
  have h_d : d = 13 / 15 := by
    have h₀' : 3 * a = b + c + d := h₀
    rw [h_a, h_b, h_c] at h₀'
    linarith
  rw [h_d]
  norm_num
