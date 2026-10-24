import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have h25 : f (25 : ℚ) = 10 := by
    have : f (25 : ℚ) = f (5 * 5 : ℚ) := by norm_num
    rw [this]
    have h_fmul : f (5 * 5 : ℚ) = f 5 + f 5 := by
      apply h₀
      <;> norm_num
    rw [h_fmul]
    have h_f5 : f (5 : ℚ) = 5 := h₁ 5 (by decide)
    rw [h_f5]
    norm_num
  have h11 : f (11 : ℚ) = 11 := h₁ 11 (by decide)
  have h_div : f ((25 : ℚ) / 11) = f (25 : ℚ) - f (11 : ℚ) := by
    have h_recip : f ((11 : ℚ)⁻¹) = -f (11 : ℚ) := by
      have h_mul_one : f ((11 : ℚ) * (11 : ℚ)⁻¹) = f (1 : ℚ) := by congr; field_simp
      have h_one : f (1 : ℚ) = 0 := by
        have : f (1 * 1 : ℚ) = f 1 + f 1 := by
          apply h₀
          <;> norm_num
        have : f (1 * 1 : ℚ) = f 1 := by norm_num
        linarith
      have h_pos : (11 : ℚ) > 0 := by norm_num
      have h_pos_inv : (11 : ℚ)⁻¹ > 0 := by positivity
      have h_mul : f ((11 : ℚ) * (11 : ℚ)⁻¹) = f (11 : ℚ) + f ((11 : ℚ)⁻¹) := by
        apply h₀
        <;> norm_num
      linarith
    have h_div_eq : f ((25 : ℚ) / 11) = f (25 : ℚ) + f ((11 : ℚ)⁻¹) := by
      have : (25 : ℚ) / 11 = (25 : ℚ) * (11 : ℚ)⁻¹ := by field_simp
      rw [this]
      have h_pos_25 : (25 : ℚ) > 0 := by norm_num
      have h_pos_inv : (11 : ℚ)⁻¹ > 0 := by positivity
      have h_mul2 : f ((25 : ℚ) * (11 : ℚ)⁻¹) = f (25 : ℚ) + f ((11 : ℚ)⁻¹) := by
        apply h₀
        <;> norm_num
      exact h_mul2
    rw [h_div_eq]
    rw [h_recip]
    ring
  rw [h_div]
  rw [h25, h11]
  norm_num
