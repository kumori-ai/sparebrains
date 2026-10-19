import Mathlib

open scoped Nat
open scoped Real

/--
Seven cubes, whose volumes are $1$, $8$, $27$, $64$, $125$, $216$, and $343$ cubic units, are stacked vertically to form a tower in which the volumes of the cubes decrease from bottom to top. Except for the bottom cube, the bottom face of each cube lies completely on top of the cube below it. What is the total surface area of the tower (including the bottom) in square units?

$\textbf{(A) } 644    \qquad \textbf{(B) } 658   \qquad \textbf{(C) } 664   \qquad \textbf{(D) } 720   \qquad \textbf{(E) } 749$ -/
theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
  have h_main : (↑(∑ k ∈ Finset.range 7, 6 * a k ^ 2 :) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2 :)) = (658 : ℤ) := by
    have h₇ : a 0 = 1 := by
      have h₇₁ : a 0 ^ 3 = 1 := h₀
      have h₇₂ : a 0 ≤ 1 := by
        nlinarith [pow_two_nonneg (a 0 : ℕ), pow_two_nonneg (a 0 - 1 : ℕ)]
      have h₇₃ : a 0 ≥ 1 := by
        nlinarith [pow_two_nonneg (a 0 : ℕ), pow_two_nonneg (a 0 - 1 : ℕ)]
      interval_cases a 0 <;> norm_num at h₇₁ ⊢ <;> nlinarith
    have h₈ : a 1 = 2 := by
      have h₈₁ : a 1 ^ 3 = 8 := h₁
      have h₈₂ : a 1 ≤ 2 := by
        nlinarith [pow_two_nonneg (a 1 : ℕ), pow_two_nonneg (a 1 - 1 : ℕ), pow_two_nonneg (a 1 - 2 : ℕ)]
      have h₈₃ : a 1 ≥ 2 := by
        nlinarith [pow_two_nonneg (a 1 : ℕ), pow_two_nonneg (a 1 - 1 : ℕ), pow_two_nonneg (a 1 - 2 : ℕ)]
      interval_cases a 1 <;> norm_num at h₈₁ ⊢ <;> nlinarith
    have h₉ : a 2 = 3 := by
      have h₉₁ : a 2 ^ 3 = 27 := h₂
      have h₉₂ : a 2 ≤ 3 := by
        nlinarith [pow_two_nonneg (a 2 : ℕ), pow_two_nonneg (a 2 - 1 : ℕ), pow_two_nonneg (a 2 - 2 : ℕ), pow_two_nonneg (a 2 - 3 : ℕ)]
      have h₉₃ : a 2 ≥ 3 := by
        nlinarith [pow_two_nonneg (a 2 : ℕ), pow_two_nonneg (a 2 - 1 : ℕ), pow_two_nonneg (a 2 - 2 : ℕ), pow_two_nonneg (a 2 - 3 : ℕ)]
      interval_cases a 2 <;> norm_num at h₉₁ ⊢ <;> nlinarith
    have h₁₀ : a 3 = 4 := by
      have h₁₀₁ : a 3 ^ 3 = 64 := h₃
      have h₁₀₂ : a 3 ≤ 4 := by
        nlinarith [pow_two_nonneg (a 3 : ℕ), pow_two_nonneg (a 3 - 1 : ℕ), pow_two_nonneg (a 3 - 2 : ℕ), pow_two_nonneg (a 3 - 3 : ℕ), pow_two_nonneg (a 3 - 4 : ℕ)]
      have h₁₀₃ : a 3 ≥ 4 := by
        nlinarith [pow_two_nonneg (a 3 : ℕ), pow_two_nonneg (a 3 - 1 : ℕ), pow_two_nonneg (a 3 - 2 : ℕ), pow_two_nonneg (a 3 - 3 : ℕ), pow_two_nonneg (a 3 - 4 : ℕ)]
      interval_cases a 3 <;> norm_num at h₁₀₁ ⊢ <;> nlinarith
    have h₁₁ : a 4 = 5 := by
      have h₁₁₁ : a 4 ^ 3 = 125 := h₄
      have h₁₁₂ : a 4 ≤ 5 := by
        nlinarith [pow_two_nonneg (a 4 : ℕ), pow_two_nonneg (a 4 - 1 : ℕ), pow_two_nonneg (a 4 - 2 : ℕ), pow_two_nonneg (a 4 - 3 : ℕ), pow_two_nonneg (a 4 - 4 : ℕ), pow_two_nonneg (a 4 - 5 : ℕ)]
      have h₁₁₃ : a 4 ≥ 5 := by
        nlinarith [pow_two_nonneg (a 4 : ℕ), pow_two_nonneg (a 4 - 1 : ℕ), pow_two_nonneg (a 4 - 2 : ℕ), pow_two_nonneg (a 4 - 3 : ℕ), pow_two_nonneg (a 4 - 4 : ℕ), pow_two_nonneg (a 4 - 5 : ℕ)]
      interval_cases a 4 <;> norm_num at h₁₁₁ ⊢ <;> nlinarith
    have h₁₂ : a 5 = 6 := by
      have h₁₂₁ : a 5 ^ 3 = 216 := h₅
      have h₁₂₂ : a 5 ≤ 6 := by
        nlinarith [pow_two_nonneg (a 5 : ℕ), pow_two_nonneg (a 5 - 1 : ℕ), pow_two_nonneg (a 5 - 2 : ℕ), pow_two_nonneg (a 5 - 3 : ℕ), pow_two_nonneg (a 5 - 4 : ℕ), pow_two_nonneg (a 5 - 5 : ℕ), pow_two_nonneg (a 5 - 6 : ℕ)]
      have h₁₂₃ : a 5 ≥ 6 := by
        nlinarith [pow_two_nonneg (a 5 : ℕ), pow_two_nonneg (a 5 - 1 : ℕ), pow_two_nonneg (a 5 - 2 : ℕ), pow_two_nonneg (a 5 - 3 : ℕ), pow_two_nonneg (a 5 - 4 : ℕ), pow_two_nonneg (a 5 - 5 : ℕ), pow_two_nonneg (a 5 - 6 : ℕ)]
      interval_cases a 5 <;> norm_num at h₁₂₁ ⊢ <;> nlinarith
    have h₁₃ : a 6 = 7 := by
      have h₁₃₁ : a 6 ^ 3 = 343 := h₆
      have h₁₃₂ : a 6 ≤ 7 := by
        nlinarith [pow_two_nonneg (a 6 : ℕ), pow_two_nonneg (a 6 - 1 : ℕ), pow_two_nonneg (a 6 - 2 : ℕ), pow_two_nonneg (a 6 - 3 : ℕ), pow_two_nonneg (a 6 - 4 : ℕ), pow_two_nonneg (a 6 - 5 : ℕ), pow_two_nonneg (a 6 - 6 : ℕ), pow_two_nonneg (a 6 - 7 : ℕ)]
      have h₁₃₃ : a 6 ≥ 7 := by
        nlinarith [pow_two_nonneg (a 6 : ℕ), pow_two_nonneg (a 6 - 1 : ℕ), pow_two_nonneg (a 6 - 2 : ℕ), pow_two_nonneg (a 6 - 3 : ℕ), pow_two_nonneg (a 6 - 4 : ℕ), pow_two_nonneg (a 6 - 5 : ℕ), pow_two_nonneg (a 6 - 6 : ℕ), pow_two_nonneg (a 6 - 7 : ℕ)]
      interval_cases a 6 <;> norm_num at h₁₃₁ ⊢ <;> nlinarith
    simp [h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    <;> norm_num <;> ring_nf <;> norm_cast <;> omega
  exact h_main
