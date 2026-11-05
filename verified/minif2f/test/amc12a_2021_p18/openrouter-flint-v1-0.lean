import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have h1 : f (1 : ℚ) = 0 := by
    have h := h₀ (1 : ℚ) (by norm_num) (1 : ℚ) (by norm_num)
    have hmul : (1 : ℚ) * (1 : ℚ) = (1 : ℚ) := by norm_num
    rw [hmul] at h
    linarith
  have h5 : f (5 : ℚ) = (5 : ℝ) := by
    have h := h₁ (5 : ℕ) (by norm_num)
    exact h
  have h11 : f (11 : ℚ) = (11 : ℝ) := by
    have h := h₁ (11 : ℕ) (by norm_num)
    exact h
  have h25 : f (25 : ℚ) = 10 := by
    have h := h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
    have hmul : (5 : ℚ) * (5 : ℚ) = (25 : ℚ) := by norm_num
    rw [hmul] at h
    rw [h5] at h
    norm_num at h
    exact h
  have h11inv : f (1 / 11) = - f (11 : ℚ) := by
    have h := h₀ (11 : ℚ) (by norm_num) (1 / 11) (by positivity)
    have hmul : (11 : ℚ) * (1 / 11) = (1 : ℚ) := by norm_num
    rw [hmul] at h
    rw [h1] at h
    linarith
  have h25div : f ((25 : ℚ) / 11) = f (25 : ℚ) + f (1 / 11) := by
    have h := h₀ (25 : ℚ) (by norm_num) (1 / 11) (by positivity)
    have hmul : (25 : ℚ) * (1 / 11) = (25 : ℚ) / 11 := by norm_num
    rw [hmul] at h
    exact h
  have hfinal : f ((25 : ℚ) / 11) = -1 := by
    rw [h25div, h11inv, h25, h11]
    norm_num
  linarith
