import Mathlib

open scoped Nat
open scoped Real

/--
Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h4 : 4 * a = 5 * b := by
    linarith [h₀, h₁]
  have h5 : 4 * a = 3 * c := by
    linarith [h₀, h₂]
  have ha : a = 1 := by
    have h6 : 24 * a = 24 := by
      linarith [h₃, h4, h5]
    linarith
  have hb : b = 4 / 5 := by
    linarith [h4, ha]
  have hc : c = 4 / 3 := by
    linarith [h5, ha]
  have hd : d = 13 / 15 := by
    linarith [h₀, ha, hb, hc]
  rw [hd]
  norm_num
