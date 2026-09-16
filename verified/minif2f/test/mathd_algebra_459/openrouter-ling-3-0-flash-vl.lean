import Mathlib

open scoped Nat
open scoped Real

/--
Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h4 : 4 * a = 5 * b := by linarith [h₀, h₁]
  have h5 : 4 * a = 3 * c := by linarith [h₀, h₂]
  have hb : b = 4 * a / 5 := by
    calc b = (5 * b) / 5 := by ring
      _ = (4 * a) / 5 := by rw [h4]
  have hc : c = 4 * a / 3 := by
    calc c = (3 * c) / 3 := by ring
      _ = (4 * a) / 3 := by rw [h5]
  have h6 : 8 * a + 10 * (4 * a / 5) + 6 * (4 * a / 3) = 24 := by
    rw [hb, hc] at h₃
    exact h₃
  have h7 : a = 1 := by
    have h8 : 10 * (4 * a / 5) = 8 * a := by ring
    have h9 : 6 * (4 * a / 3) = 8 * a := by ring
    linarith [h6, h8, h9]
  have h8 : b = 4 / 5 := by linarith [hb, h7]
  have h9 : c = 4 / 3 := by linarith [hc, h7]
  have hd : d = 13 / 15 := by
    rw [h7] at h₀
    have h_temp : d = 3 - b - c := by linarith [h₀]
    rw [h8, h9] at h_temp
    linarith
  have h_den : d.den = 15 := by
    rw [hd]
    norm_num
  have h_num : d.num = 13 := by
    rw [hd]
    norm_num
  linarith
