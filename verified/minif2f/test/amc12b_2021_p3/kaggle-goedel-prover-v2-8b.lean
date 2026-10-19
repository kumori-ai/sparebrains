import Mathlib

open scoped Nat
open scoped Real

/-- Suppose $$2+\frac{1}{1+\frac{1}{2+\frac{2}{3+x}}}=\frac{144}{53}.$$ What is the value of $x?$

$\textbf{(A) }\frac34 \qquad \textbf{(B) }\frac78 \qquad \textbf{(C) }\frac{14}{15} \qquad \textbf{(D) }\frac{37}{38} \qquad \textbf{(E) }\frac{52}{53}$ -/
theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 := by
  have h₁ : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := by
    by_contra h
    have h₂ : 1 + 1 / (2 + 2 / (3 + x)) = 0 := by simpa using h
    have h₃ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 2 + 1 / 0 := by rw [h₂] <;> simp
    have h₄ : (2 : ℝ) + 1 / 0 = 2 := by norm_num
    rw [h₃, h₄] at h₀
    norm_num at h₀
    <;> linarith
  
  have h₂ : 2 + 2 / (3 + x) ≠ 0 := by
    by_contra h
    have h₃ : 2 + 2 / (3 + x) = 0 := by simpa using h
    have h₄ : 1 + 1 / (2 + 2 / (3 + x)) = 1 + 1 / 0 := by rw [h₃] <;> simp
    have h₅ : (1 : ℝ) + 1 / 0 = 1 := by norm_num
    have h₆ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 2 + 1 / 1 := by
      rw [h₄, h₅]
      <;> simp
    rw [h₆] at h₀
    norm_num at h₀
    <;> linarith
  
  have h₃ : 3 + x ≠ 0 := by
    by_contra h
    have h₄ : 3 + x = 0 := by simpa using h
    have h₅ : 2 + 2 / (3 + x) = 2 + 2 / 0 := by rw [h₄] <;> simp
    have h₆ : (2 : ℝ) + 2 / 0 = 2 := by norm_num
    have h₇ : 1 + 1 / (2 + 2 / (3 + x)) = 1 + 1 / 2 := by
      rw [h₅, h₆]
      <;> norm_num
    have h₈ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 2 + 1 / (1 + 1 / 2) := by
      rw [h₇]
    rw [h₈] at h₀
    norm_num at h₀
    <;> linarith
  
  have h₄ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 38 / 53 := by
    have h₅ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 := h₀
    have h₆ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 - 2 := by linarith
    rw [h₆]
    <;> norm_num
    <;> linarith
  
  have h₅ : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
    have h₅₁ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 38 / 53 := h₄
    have h₅₂ : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := h₁
    have h₅₃ : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
      have h₅₄ : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := by
        have h₅₅ : 1 / (1 + 1 / (2 + 2 / (3 + x))) = 38 / 53 := h₄
        have h₅₆ : 1 + 1 / (2 + 2 / (3 + x)) ≠ 0 := h₁
        have h₅₇ : (1 + 1 / (2 + 2 / (3 + x))) = 53 / 38 := by
          apply_fun (fun x => 1 / x) at h₅₅
          <;> field_simp at h₅₅ ⊢
          <;> nlinarith
        exact h₅₇
      exact h₅₄
    exact h₅₃
  
  have h₆ : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by
    have h₆₁ : 1 + 1 / (2 + 2 / (3 + x)) = 53 / 38 := h₅
    have h₆₂ : 1 / (2 + 2 / (3 + x)) = 15 / 38 := by
      linarith
    exact h₆₂
  
  have h₇ : 2 + 2 / (3 + x) = 38 / 15 := by
    have h₇₁ : 1 / (2 + 2 / (3 + x)) = 15 / 38 := h₆
    have h₇₂ : 2 + 2 / (3 + x) ≠ 0 := h₂
    have h₇₃ : 2 + 2 / (3 + x) = 38 / 15 := by
      have h₇₄ : 2 + 2 / (3 + x) = 38 / 15 := by
        have h₇₅ : 1 / (2 + 2 / (3 + x)) = 15 / 38 := h₆
        have h₇₆ : 2 + 2 / (3 + x) ≠ 0 := h₂
        have h₇₇ : (2 + 2 / (3 + x)) = 38 / 15 := by
          apply_fun (fun x => 1 / x) at h₇₅
          <;> field_simp at h₇₅ ⊢
          <;> nlinarith
        exact h₇₇
      exact h₇₄
    exact h₇₃
  
  have h₈ : 2 / (3 + x) = 8 / 15 := by
    have h₈₁ : 2 + 2 / (3 + x) = 38 / 15 := h₇
    have h₈₂ : 2 / (3 + x) = 8 / 15 := by
      linarith
    exact h₈₂
  
  have h₉ : 3 + x = 15 / 4 := by
    have h₉₁ : 2 / (3 + x) = 8 / 15 := h₈
    have h₉₂ : 3 + x ≠ 0 := h₃
    have h₉₃ : 3 + x = 15 / 4 := by
      have h₉₄ : 3 + x = 15 / 4 := by
        have h₉₅ : 2 / (3 + x) = 8 / 15 := h₈
        have h₉₆ : 3 + x ≠ 0 := h₃
        have h₉₇ : (3 + x) = 15 / 4 := by
          have h₉₈ : (3 + x) ≠ 0 := h₃
          field_simp at h₉₅ ⊢
          <;> ring_nf at h₉₅ ⊢ <;> nlinarith
        exact h₉₇
      exact h₉₄
    exact h₉₃
  
  have h₁₀ : x = 3 / 4 := by
    have h₁₀₁ : 3 + x = 15 / 4 := h₉
    have h₁₀₂ : x = 3 / 4 := by linarith
    exact h₁₀₂
  
  exact h₁₀
