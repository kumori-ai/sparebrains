import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have h₂ : f ((25 : ℚ) / 11) = f (25 : ℚ) - f (11 : ℚ) := by
    have h₃ : f ((25 : ℚ) / 11 * (11 : ℚ)) = f ((25 : ℚ) / 11) + f (11 : ℚ) := by
      apply h₀
      · norm_num
      · norm_num
    have h₄ : f ((25 : ℚ) / 11 * (11 : ℚ)) = f (25 : ℚ) := by
      norm_num
    rw [h₄] at h₃
    linarith
  have h₅ : f (25 : ℚ) = 10 := by
    have h₆ : f (25 : ℚ) = f (5 : ℚ) + f (5 : ℚ) := by
      have h₇ : f ((5 : ℚ) * (5 : ℚ)) = f (5 : ℚ) + f (5 : ℚ) := by
        apply h₀
        · norm_num
        · norm_num
      norm_num at h₇ ⊢
      exact h₇
    have h₈ : f (5 : ℚ) = 5 := by
      have h₉ : Nat.Prime 5 := by decide
      have h₁₀ : f (5 : ℚ) = (5 : ℝ) := h₁ 5 h₉
      exact_mod_cast h₁₀
    rw [h₆, h₈]
    norm_num
  have h₁₂ : f (11 : ℚ) = 11 := by
    have h₁₃ : Nat.Prime 11 := by decide
    have h₁₄ : f (11 : ℚ) = (11 : ℝ) := h₁ 11 h₁₃
    exact_mod_cast h₁₄
  rw [h₂, h₅, h₁₂]
  norm_num
