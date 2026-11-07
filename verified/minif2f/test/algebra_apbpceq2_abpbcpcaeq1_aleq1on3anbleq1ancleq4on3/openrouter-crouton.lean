import Mathlib

open scoped Nat
open scoped Real

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  set x := a - 1 with hx_def
  set y := b - 1 with hy_def
  set z := c - 1 with hz_def
  have hx_sum : x + y + z = -1 := by
    rw [hx_def, hy_def, hz_def]
    linarith [h₁]
  have hpair : x * y + y * z + z * x = 0 := by
    rw [hx_def, hy_def, hz_def]
    linear_combination h₂ - 2 * h₁
  have hxy : x ≤ y := by
    rw [hx_def, hy_def]
    linarith [h₀.1]
  have hyz : y ≤ z := by
    rw [hy_def, hz_def]
    linarith [h₀.2]
  have hz0 : 0 ≤ z := by
    by_contra h
    push_neg at h
    have hx_lt : x < 0 := lt_of_le_of_lt (le_trans hxy hyz) h
    have hy_lt : y < 0 := lt_of_le_of_lt hyz h
    have h1 : 0 < x * y := mul_pos_of_neg_of_neg hx_lt hy_lt
    have h2 : 0 < y * z := mul_pos_of_neg_of_neg hy_lt h
    have h3 : 0 < z * x := mul_pos_of_neg_of_neg h hx_lt
    linarith [hpair]
  have hxy_eq : x * y = z + z ^ 2 := by
    linear_combination hpair - z * hx_sum
  have hxy_nonneg : 0 ≤ x * y := by
    rw [hxy_eq]
    nlinarith [hz0, sq_nonneg z]
  have hy0 : y ≤ 0 := by
    by_contra h
    push_neg at h
    have hx0 : 0 ≤ x := by
      by_contra hx
      push_neg at hx
      have hneg : x * y < 0 := mul_neg_of_neg_of_pos hx h
      linarith [hxy_nonneg]
    linarith [hx_sum, hz0, hx0, h]
  have hx0 : x ≤ 0 := le_trans hxy hy0
  have hx_lt : x < 0 := by
    rcases eq_or_lt_of_le hx0 with h | h
    · exfalso
      have hy_eq : y = 0 := by linarith [hxy, hy0, h]
      have hz_eq : z = -1 := by linarith [hx_sum, h, hy_eq]
      linarith [hz0]
    · exact h
  have hx_ge : -1 ≤ x := by
    have heq : (y - z) ^ 2 = (1 + x) * (1 - 3 * x) := by
      linear_combination (3 * x + y + z - 1) * hx_sum - 4 * hpair
    have hnonneg : 0 ≤ (1 + x) * (1 - 3 * x) := by
      rw [← heq]
      exact sq_nonneg _
    by_contra h
    push_neg at h
    have hneg : (1 + x) * (1 - 3 * x) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith [hx0])
    linarith
  have hz_le : z ≤ 1 / 3 := by
    have heq : (x - y) ^ 2 = (1 + z) * (1 - 3 * z) := by
      linear_combination (x + y + 3 * z - 1) * hx_sum - 4 * hpair
    have hnonneg : 0 ≤ (1 + z) * (1 - 3 * z) := by
      rw [← heq]
      exact sq_nonneg _
    by_contra h
    push_neg at h
    have hneg : (1 + z) * (1 - 3 * z) < 0 :=
      mul_neg_of_pos_of_neg (by linarith [hz0]) (by linarith)
    linarith
  have hx_le : x ≤ -2 / 3 := by
    have heq : (y - x) * (z - x) = x * (2 + 3 * x) := by
      linear_combination hpair - 2 * x * hx_sum
    have hnonneg : 0 ≤ x * (2 + 3 * x) := by
      rw [← heq]
      exact mul_nonneg (by linarith [hxy]) (by linarith [hxy, hyz])
    by_contra h
    push_neg at h
    have hneg : x * (2 + 3 * x) < 0 :=
      mul_neg_of_neg_of_pos hx_lt (by linarith)
    linarith
  have hy_ge : -2 / 3 ≤ y := by
    have heq : (x - y) * (z - y) = y * (2 + 3 * y) := by
      linear_combination hpair - 2 * y * hx_sum
    have hnonpos : y * (2 + 3 * y) ≤ 0 := by
      rw [← heq]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hxy]) (by linarith [hyz])
    by_contra h
    push_neg at h
    have hpos : 0 < y * (2 + 3 * y) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  exact ⟨by linarith [hx_def, hx_ge], by linarith [hx_def, hx_le],
    by linarith [hy_def, hy_ge], by linarith [hy_def, hy0],
    by linarith [hz_def, hz0], by linarith [hz_def, hz_le]⟩
