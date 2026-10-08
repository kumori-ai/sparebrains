import Mathlib

open scoped Nat
open scoped Real

/--
Given a nonnegative real number $x,$ let $\langle x\rangle$ denote the fractional part of $x;$ that is, $\langle x\rangle=x-\lfloor x\rfloor,$ where $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x.$  Suppose that $a$ is positive, $\langle a^{-1}\rangle=\langle a^2\rangle,$ and $2< a^2< 3.$  Find the value of $a^{12}-144a^{-1}.$ -/
theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by
  have h_floor_a2 : Int.floor (a ^ 2) = 2 := by
    have h₄ : (2 : ℝ) < a ^ 2 := by exact_mod_cast h₂
    have h₅ : (a : ℝ) ^ 2 < 3 := by exact_mod_cast h₃
    have h₆ : Int.floor (a ^ 2) = 2 := by
      rw [Int.floor_eq_iff]
      norm_num at h₄ h₅ ⊢
      constructor <;> norm_num <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try nlinarith)
    exact h₆
  
  have h_floor_1a : Int.floor (1 / a) = 0 := by
    have h₄ : 0 < 1 / a := by positivity
    have h₅ : 1 / a < 1 := by
      have h₅₁ : 0 < a := h₀
      have h₅₂ : 0 < a ^ 2 := by positivity
      have h₅₃ : 2 < a ^ 2 := h₂
      have h₅₄ : 0 < a ^ 2 := by positivity
      have h₅₅ : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      exact h₅₅
    have h₆ : Int.floor (1 / a) = 0 := by
      rw [Int.floor_eq_iff]
      norm_num at h₄ h₅ ⊢
      <;>
      (try constructor <;> norm_num <;> linarith) <;>
      (try linarith)
    exact h₆
  
  have h_eq : 1 / a = a ^ 2 - 2 := by
    have h₄ : (Int.floor (a ^ 2) : ℝ) = 2 := by
      norm_cast
      <;> simp [h_floor_a2]
    have h₅ : (Int.floor (1 / a) : ℝ) = 0 := by
      norm_cast
      <;> simp [h_floor_1a]
    have h₆ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2) := h₁
    have h₇ : (1 / a : ℝ) - (Int.floor (1 / a) : ℝ) = (a ^ 2 : ℝ) - (Int.floor (a ^ 2) : ℝ) := by
      norm_cast at h₆ ⊢
      <;> simp_all [h₄, h₅]
      <;> linarith
    have h₈ : (1 / a : ℝ) - 0 = (a ^ 2 : ℝ) - 2 := by
      rw [h₅] at h₇
      rw [h₄] at h₇
      linarith
    have h₉ : (1 / a : ℝ) = (a ^ 2 : ℝ) - 2 := by linarith
    omega
  have h_poly : a ^ 3 - 2 * a - 1 = 0 := by
    have h₄ : 1 / a = a ^ 2 - 2 := h_eq
    have h₅ : a ≠ 0 := by linarith
    have h₆ : a ^ 3 - 2 * a - 1 = 0 := by
      have h₇ : 1 = (a ^ 2 - 2) * a := by
        field_simp [h₅] at h₄ ⊢
        nlinarith
      nlinarith
    exact h₆
  
  have h_a2 : a ^ 2 = a + 1 := by
    have h₄ : a ^ 3 - 2 * a - 1 = 0 := h_poly
    have h₅ : a ^ 2 - a - 1 = 0 := by
      have h₆ : a ^ 3 - 2 * a - 1 = (a + 1) * (a ^ 2 - a - 1) := by
        ring_nf
        <;>
        nlinarith
      have h₇ : (a + 1 : ℝ) ≠ 0 := by
        nlinarith
      have h₈ : (a + 1 : ℝ) * (a ^ 2 - a - 1) = 0 := by
        linarith
      have h₉ : (a ^ 2 - a - 1 : ℝ) = 0 := by
        apply mul_left_cancel₀ (show (a + 1 : ℝ) ≠ 0 by linarith)
        linarith
      linarith
    nlinarith
  
  have h_a4 : a ^ 4 = 2 * a ^ 2 + a := by
    have h₄ : a ^ 3 = 2 * a + 1 := by
      have h₅ : a ^ 3 - 2 * a - 1 = 0 := h_poly
      linarith
    calc
      a ^ 4 = a * a ^ 3 := by ring
      _ = a * (2 * a + 1) := by rw [h₄]
      _ = 2 * a ^ 2 + a := by ring
  
  have h_a5 : a ^ 5 = 2 * a ^ 3 + a ^ 2 := by
    calc
      a ^ 5 = a * a ^ 4 := by ring
      _ = a * (2 * a ^ 2 + a) := by rw [h_a4]
      _ = 2 * a ^ 3 + a ^ 2 := by ring
  
  have h_a6 : a ^ 6 = 4 * a ^ 2 + 4 * a + 1 := by
    calc
      a ^ 6 = a * a ^ 5 := by ring
      _ = a * (2 * a ^ 3 + a ^ 2) := by rw [h_a5]
      _ = 2 * a ^ 4 + a ^ 3 := by ring
      _ = 2 * (2 * a ^ 2 + a) + (2 * a + 1) := by
        linarith
      _ = 4 * a ^ 2 + 2 * a + 2 * a + 1 := by ring
      _ = 4 * a ^ 2 + 4 * a + 1 := by ring
  
  have h_a12 : a ^ 12 = 56 * a ^ 2 + 88 * a + 33 := by
    calc
      a ^ 12 = (a ^ 6) ^ 2 := by ring
      _ = (4 * a ^ 2 + 4 * a + 1) ^ 2 := by rw [h_a6]
      _ = 16 * a ^ 4 + 32 * a ^ 3 + 16 * a ^ 2 + 8 * a ^ 2 + 8 * a + 1 := by
        ring_nf
        <;>
        nlinarith
      _ = 16 * (2 * a ^ 2 + a) + 32 * (2 * a + 1) + 16 * a ^ 2 + 8 * a ^ 2 + 8 * a + 1 := by
        linarith
      _ = 32 * a ^ 2 + 16 * a + 64 * a + 32 + 16 * a ^ 2 + 8 * a ^ 2 + 8 * a + 1 := by
        ring_nf
        <;>
        nlinarith
      _ = 56 * a ^ 2 + 88 * a + 33 := by
        ring_nf
        <;>
        nlinarith
  
  have h_main : a ^ 12 - 144 * (1 / a) = 233 := by
    have h₄ : 1 / a = a ^ 2 - 2 := h_eq
    have h₅ : a ^ 2 = a + 1 := h_a2
    have h₆ : a ^ 12 = 56 * a ^ 2 + 88 * a + 33 := h_a12
    calc
      a ^ 12 - 144 * (1 / a) = (56 * a ^ 2 + 88 * a + 33) - 144 * (1 / a) := by rw [h₆]
      _ = (56 * a ^ 2 + 88 * a + 33) - 144 * (a ^ 2 - 2) := by
        rw [h₄]
        <;> ring_nf
      _ = (56 * a ^ 2 + 88 * a + 33) - (144 * a ^ 2 - 288) := by ring_nf
      _ = -88 * a ^ 2 + 88 * a + 321 := by ring_nf
      _ = 233 := by
        have h₇ : a ^ 2 = a + 1 := h_a2
        rw [h₇]
        ring_nf
        <;> nlinarith [sq_nonneg (a - 1)]
  
  exact h_main
