import Mathlib

open scoped Nat
open scoped Real

/--
Suppose $a,b,c$ are the sides of a triangle. Prove that \[ a^2(b+c-a)+b^2(a+c-b)+c^2(a+b-c) \leq 3abc  \] -/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have ha_pos : 0 < a := h₀.1
  have hb_pos : 0 < b := h₀.2.1
  have hc_pos : 0 < c := h₀.2.2
  have hab_pos : 0 < a + b := add_pos ha_pos hb_pos
  have hac_pos : 0 < a + c := add_pos ha_pos hc_pos
  have hbc_pos : 0 < b + c := add_pos hb_pos hc_pos
  have t1_pos : 0 < b + c - a := by
    have : a < b + c := h₃
    linarith
  have t2_pos : 0 < c + a - b := by
    have : b < a + c := h₂
    linarith
  have t3_pos : 0 < a + b - c := by
    have : c < a + b := h₁
    linarith
  have hab_pos' : 0 < a + b - c := t3_pos
  have hac_pos' : 0 < c + a - b := t2_pos
  have hbc_pos' : 0 < b + c - a := t1_pos
  ring_nf
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_pos ha_pos hb_pos, mul_pos hb_pos hc_pos, mul_pos hc_pos ha_pos]
