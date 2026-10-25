import Mathlib

open scoped Nat
open scoped Real

/--
Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have hb : b = 4 / 5 := by
    have h_c : c = 5 * b / 3 := by
      have h_cd : c + d = 4 * b - a := by linarith
      have h_d : d = 2 * c - a - b := by linarith
      have h_sub : c + (2 * c - a - b) = 4 * b - a := by linarith
      ring_nf at h_sub
      linarith
    have h_d : d = 7 * b / 3 - a := by
      rw [h_c] at h₂
      linarith
    have h_a : a = 5 * b / 4 := by
      have h_sub : b + c + d = 3 * a := by linarith
      rw [h_c, h_d] at h_sub
      ring_nf at h_sub
      linarith
    have h_sub : 8 * a + 10 * b + 6 * c = 24 := h₃
    rw [h_a, h_c] at h_sub
    ring_nf at h_sub
    linarith
  have hd : d = 13 / 15 := by
    have h_c : c = 5 * b / 3 := by
      have h_cd : c + d = 4 * b - a := by linarith
      have h_d : d = 2 * c - a - b := by linarith
      have h_sub : c + (2 * c - a - b) = 4 * b - a := by linarith
      ring_nf at h_sub
      linarith
    have h_d : d = 7 * b / 3 - a := by
      rw [h_c] at h₂
      linarith
    have h_a : a = 5 * b / 4 := by
      have h_sub : b + c + d = 3 * a := by linarith
      rw [h_c, h_d] at h_sub
      ring_nf at h_sub
      linarith
    rw [hb] at h_a
    norm_num at h_a
    have h_d' : d = 7 * (4 / 5 : ℚ) / 3 - a := by
      rw [hb] at h_d
      norm_num
      linarith
    rw [h_a] at h_d'
    norm_num at h_d'
    linarith
  have h_num : d.num = 13 := by
    rw [hd]
    norm_num
  have h_den : d.den = 15 := by
    rw [hd]
    norm_num
  linarith
