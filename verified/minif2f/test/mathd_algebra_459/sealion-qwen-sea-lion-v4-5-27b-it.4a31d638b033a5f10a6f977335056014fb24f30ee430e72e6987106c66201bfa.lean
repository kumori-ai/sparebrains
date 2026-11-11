import Mathlib

open scoped Nat
open scoped Real

/--
Anna, Bertram, Carli, and David have a competition to see which of them can hold their breath for the longest time period, in minutes. If Bertram, Carli, and David add their times together, the resulting sum is three times the length of time that Anna can hold her breath. Similarly, if Anna, Carli, and David sum their times, the result is four times Bertram's time period, and if Anna, Bertram, and David sum their times, the result is twice Carli's time. Finally, eight times Anna's time plus ten times Bertram's time plus six times Carli's time equals two fifths of an hour. If the length of time that David can hold his breath is expressed in minutes as a simplified fraction, what is the sum of the numerator and the denominator? -/
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have h₄ : d = 13 / 15 := by
    have h₄₁ : 4 * a = a + b + c + d := by linarith
    have h₄₂ : 5 * b = a + b + c + d := by linarith
    have h₄₃ : 3 * c = a + b + c + d := by linarith
    have h₄₄ : 6 * (a + b + c + d) = 24 := by
      have h₄₅ : 8 * a + 10 * b + 6 * c = 24 := h₃
      have h₄₆ : 8 * a + 10 * b + 6 * c = 2 * (4 * a) + 2 * (5 * b) + 2 * (3 * c) := by ring
      rw [h₄₆] at h₄₅
      have h₄₇ : 2 * (4 * a) + 2 * (5 * b) + 2 * (3 * c) = 6 * (a + b + c + d) := by
        rw [h₄₁, h₄₂, h₄₃]
        <;> ring
      rw [h₄₇] at h₄₅
      linarith
    have h₄₈ : a + b + c + d = 4 := by linarith
    have h₄₉ : 4 * a = 4 := by linarith
    have h₅₀ : a = 1 := by linarith
    have h₅₁ : 5 * b = 4 := by linarith
    have h₅₂ : b = 4 / 5 := by field_simp at h₅₁ ⊢; linarith
    have h₅₃ : 3 * c = 4 := by linarith
    have h₅₄ : c = 4 / 3 := by field_simp at h₅₃ ⊢; linarith
    have h₅₅ : 1 + 4 / 5 + 4 / 3 + d = 4 := by
      rw [h₅₀, h₅₂, h₅₄] at h₄₈
      exact h₄₈
    linarith
  have h₅ : d.num = 13 ∧ d.den = 15 := by
    rw [h₄]
    constructor <;> norm_num
  rw [h₅.2, h₅.1]
  norm_num
