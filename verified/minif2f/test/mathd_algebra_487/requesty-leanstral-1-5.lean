import Mathlib

open scoped Nat
open scoped Real

/-- What is the distance between the two intersections of $y=x^2$ and $x+y=1$? -/
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have ha_eq : a ^ 2 + a = 1 := by
    calc
      a ^ 2 + a = a + a ^ 2 := add_comm _ _
      _ = a + b := by rw [h₀]
      _ = 1 := h₁
  have hc_eq : c ^ 2 + c = 1 := by
    calc
      c ^ 2 + c = c + c ^ 2 := add_comm _ _
      _ = c + d := by rw [h₂]
      _ = 1 := h₃
  have h_factor : (a - c) * (a + c + 1) = 0 := by
    calc
      (a - c) * (a + c + 1) = (a - c) * (a + c) + (a - c) := by ring
      _ = (a ^ 2 - c ^ 2) + (a - c) := by ring
      _ = (a ^ 2 + a) - (c ^ 2 + c) := by ring
      _ = 1 - 1 := by rw [ha_eq, hc_eq]
      _ = 0 := by norm_num
  have h_sum : a + c = -1 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h | h
    · exfalso; exact h₄ (sub_eq_zero.mp h)
    · linarith
  have h_prod : a * c = -1 := by
    have h_sq_sum : (a + c) ^ 2 = a ^ 2 + 2 * a * c + c ^ 2 := by ring
    have h_sum_sq : (a + c) ^ 2 = 1 := by
      rw [h_sum]
      norm_num
    have h_a2_c2 : a ^ 2 + c ^ 2 = 3 := by
      calc
        a ^ 2 + c ^ 2 = (a ^ 2 + a) + (c ^ 2 + c) - (a + c) := by ring
        _ = 1 + 1 - (-1) := by rw [ha_eq, hc_eq, h_sum]
        _ = 3 := by norm_num
    have h_eq : a ^ 2 + 2 * a * c + c ^ 2 = 1 := by
      rw [← h_sq_sum, h_sum_sq]
    linarith
  have h_sq_diff : (a - c) ^ 2 = 5 := by
    calc
      (a - c) ^ 2 = (a + c) ^ 2 - 4 * (a * c) := by ring
      _ = (-1) ^ 2 - 4 * (-1) := by rw [h_sum, h_prod]
      _ = 1 + 4 := by norm_num
      _ = 5 := by norm_num
  have h_expr : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    calc
      (a - c) ^ 2 + (b - d) ^ 2 = (a - c) ^ 2 + (a ^ 2 - c ^ 2) ^ 2 := by rw [h₀, h₂]
      _ = (a - c) ^ 2 + ((a - c) * (a + c)) ^ 2 := by ring
      _ = (a - c) ^ 2 + ((a - c) * (-1)) ^ 2 := by rw [h_sum]
      _ = (a - c) ^ 2 + (a - c) ^ 2 := by ring
      _ = 2 * (a - c) ^ 2 := by ring
      _ = 2 * 5 := by rw [h_sq_diff]
      _ = 10 := by norm_num
  rw [h_expr]
