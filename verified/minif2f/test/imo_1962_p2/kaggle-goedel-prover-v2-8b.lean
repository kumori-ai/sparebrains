import Mathlib

open scoped Nat
open scoped Real

/--
Determine all real numbers $x$ which satisfy the inequality: \[ \sqrt{3-x}-\sqrt{x+1}>\dfrac{1}{2} \] -/
theorem imo_1962_p2 :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)} =
      Set.Ico (-1) (1 - Real.sqrt 31 / 8) := by
  have h_subset₁ : {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)} ⊆ Set.Ico (-1) (1 - Real.sqrt 31 / 8) := by
    intro x hx
    have h₁ : 0 ≤ 3 - x := hx.1
    have h₂ : 0 ≤ x + 1 := hx.2.1
    have h₃ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := hx.2.2
    have h₄ : -1 ≤ x := by linarith
    have h₅ : x < 1 - Real.sqrt 31 / 8 := by
      by_contra h
      have h₆ : x ≥ 1 - Real.sqrt 31 / 8 := by linarith
      have h₇ : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
      have h₈ : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
      have h₉ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≤ 1 / 2 := by
        have h₁₀ : x ≥ 1 - Real.sqrt 31 / 8 := h₆
        have h₁₁ : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
        have h₁₂ : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
        have h₁₃ : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by rw [Real.sq_sqrt (by linarith)]
        have h₁₄ : (Real.sqrt (3 - x)) ^ 2 = 3 - x := by rw [Real.sq_sqrt (by linarith)]
        have h₁₅ : 8 * (Real.sqrt (x + 1)) ^ 2 + 4 * Real.sqrt (x + 1) - 15 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
            Real.sqrt_nonneg (x + 1), Real.sq_sqrt (by linarith : 0 ≤ x + 1),
            sq_nonneg (Real.sqrt (x + 1) - (-1 + Real.sqrt 31) / 4)]
        nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
          Real.sqrt_nonneg (x + 1), Real.sq_sqrt (by linarith : 0 ≤ x + 1),
          sq_nonneg (Real.sqrt (x + 1) - (-1 + Real.sqrt 31) / 4),
          Real.sqrt_nonneg (3 - x), Real.sq_sqrt (by linarith : 0 ≤ 3 - x)]
      linarith
    exact ⟨by linarith, by linarith⟩
  
  have h_subset₂ : Set.Ico (-1) (1 - Real.sqrt 31 / 8) ⊆ {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)} := by
    intro x hx
    have h₁ : -1 ≤ x := hx.1
    have h₂ : x < 1 - Real.sqrt 31 / 8 := hx.2
    have h₃ : 0 ≤ 3 - x := by
      have h₃₁ : x ≤ 3 := by
        by_contra h
        have h₃₂ : x > 3 := by linarith
        have h₃₃ : x ≥ 1 - Real.sqrt 31 / 8 := by
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
        nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
      linarith
    have h₄ : 0 ≤ x + 1 := by linarith
    have h₅ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
      have h₅₁ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
      have h₅₂ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg (3 - x)
      have h₅₃ : 0 ≤ Real.sqrt 31 := Real.sqrt_nonneg 31
      have h₅₄ : 0 ≤ Real.sqrt (x + 1) * Real.sqrt (3 - x) := by positivity
      have h₅₅ : 0 < Real.sqrt 31 := by positivity
      have h₅₆ : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by
        rw [Real.sq_sqrt] <;> linarith
      have h₅₇ : (Real.sqrt (3 - x)) ^ 2 = 3 - x := by
        rw [Real.sq_sqrt] <;> linarith
      have h₅₈ : 8 * (Real.sqrt (x + 1)) ^ 2 + 4 * Real.sqrt (x + 1) - 15 < 0 := by
        have h₅₈₁ : x < 1 - Real.sqrt 31 / 8 := h₂
        have h₅₈₂ : Real.sqrt (x + 1) < (-1 + Real.sqrt 31) / 4 := by
          have h₅₈₃ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
          have h₅₈₄ : 0 ≤ Real.sqrt 31 := Real.sqrt_nonneg 31
          have h₅₈₅ : 0 ≤ Real.sqrt (x + 1) * Real.sqrt 31 := by positivity
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
            Real.sq_sqrt (by linarith : 0 ≤ x + 1), Real.sqrt_nonneg (x + 1),
            sq_nonneg (Real.sqrt (x + 1) - (-1 + Real.sqrt 31) / 4),
            Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
        nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num),
          Real.sq_sqrt (by linarith : 0 ≤ x + 1), Real.sqrt_nonneg (x + 1),
          sq_nonneg (Real.sqrt (x + 1) - (-1 + Real.sqrt 31) / 4),
          Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
      have h₅₉ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1) := by
        by_contra h₅₉₁
        have h₅₉₂ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≤ 1 / 2 := by linarith
        have h₅₉₃ : Real.sqrt (3 - x) ≤ Real.sqrt (x + 1) + 1 / 2 := by linarith
        have h₅₉₄ : (Real.sqrt (3 - x)) ^ 2 ≤ (Real.sqrt (x + 1) + 1 / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (3 - x),
            Real.sq_sqrt (by linarith : 0 ≤ x + 1),
            Real.sq_sqrt (by linarith : 0 ≤ 3 - x)]
        nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (3 - x),
          Real.sq_sqrt (by linarith : 0 ≤ x + 1),
          Real.sq_sqrt (by linarith : 0 ≤ 3 - x),
          Real.sqrt_nonneg 31, Real.sq_sqrt (show 0 ≤ 31 by norm_num)]
      exact h₅₉
    exact ⟨h₃, h₄, h₅⟩
  
  have h_main : {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)} = Set.Ico (-1) (1 - Real.sqrt 31 / 8) := by
    apply Set.Subset.antisymm
    · -- Prove the forward inclusion
      exact h_subset₁
    · -- Prove the reverse inclusion
      exact h_subset₂
  
  rw [h_main]
  <;> simp_all
  <;> norm_num
  <;> linarith [Real.sqrt_nonneg 31]
