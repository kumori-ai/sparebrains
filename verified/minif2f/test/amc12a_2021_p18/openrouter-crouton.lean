import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have hf1 : f 1 = 0 := by
    have h := h₀ (1 : ℚ) (by norm_num) (1 : ℚ) (by norm_num)
    rw [mul_one] at h
    linarith
  have hfinv : ∀ x : ℚ, x > 0 → f x⁻¹ = - f x := by
    intro x hx
    have hxinv : x⁻¹ > 0 := inv_pos.mpr hx
    have h := h₀ x hx x⁻¹ hxinv
    rw [mul_inv_cancel₀ (ne_of_gt hx)] at h
    rw [hf1] at h
    linarith
  have h5 : f (5 : ℚ) = 5 := by
    simpa using h₁ 5 (by norm_num)
  have h11 : f (11 : ℚ) = 11 := by
    simpa using h₁ 11 (by norm_num)
  have h25 : f (25 : ℚ) = 10 := by
    have h := h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
    norm_num at h
    rw [h5] at h
    linarith
  rw [div_eq_mul_inv, h₀ (25 : ℚ) (by norm_num) (11 : ℚ)⁻¹ (by positivity),
    hfinv (11 : ℚ) (by norm_num), h25, h11]
  norm_num
