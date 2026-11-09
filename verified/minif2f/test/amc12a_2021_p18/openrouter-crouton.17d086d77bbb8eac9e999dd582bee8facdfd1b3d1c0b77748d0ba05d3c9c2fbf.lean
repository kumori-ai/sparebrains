import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have hf5 : f (5 : ℚ) = (5 : ℝ) := by
    have h := h₁ 5 (by norm_num)
    push_cast at h
    exact h
  have hf11 : f (11 : ℚ) = (11 : ℝ) := by
    have h := h₁ 11 (by norm_num)
    push_cast at h
    exact h
  have hf25 : f (25 : ℚ) = (10 : ℝ) := by
    have h := h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
    rw [hf5] at h
    norm_num at h
    exact h
  have h := h₀ ((25 : ℚ) / 11) (by norm_num) (11 : ℚ) (by norm_num)
  rw [hf11] at h
  have hmul : (25 : ℚ) / 11 * 11 = 25 := by norm_num
  rw [hmul, hf25] at h
  linarith [h]
