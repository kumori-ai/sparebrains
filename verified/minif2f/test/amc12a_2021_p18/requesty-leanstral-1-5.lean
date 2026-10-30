import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a function defined on the set of positive rational numbers with the property that $f(a\cdot b)=f(a)+f(b)$ for all positive rational numbers $a$ and $b$. Suppose that $f$ also has the property that $f(p)=p$ for every prime number $p$. For which of the following numbers $x$ is $f(x)< 0?$

$\textbf{(A) } \frac{17}{32} \qquad \textbf{(B) } \frac{11}{16} \qquad \textbf{(C) } \frac{7}{9} \qquad \textbf{(D) } \frac{7}{6} \qquad \textbf{(E) } \frac{25}{11}$ -/
theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f ((25 : ℚ) / 11) < 0 := by
  have h1pos : (1 : ℚ) > 0 := by norm_num
  have h11pos : (11 : ℚ) > 0 := by norm_num
  have h25pos : (25 : ℚ) > 0 := by norm_num
  have h5pos : (5 : ℚ) > 0 := by norm_num
  have hf1 : f (1 : ℚ) = 0 := by
    have h := h₀ 1 h1pos 1 h1pos
    have h' : f (1 : ℚ) = f 1 + f 1 := by simpa [mul_one] using h
    linarith
  have hf5 : f (5 : ℚ) = (5 : ℝ) := by
    have hp : Nat.Prime 5 := by norm_num
    have h := h₁ 5 hp
    simpa using h
  have hf11 : f (11 : ℚ) = (11 : ℝ) := by
    have hp : Nat.Prime 11 := by norm_num
    have h := h₁ 11 hp
    simpa using h
  have hf25 : f (25 : ℚ) = (10 : ℝ) := by
    have h := h₀ 5 h5pos 5 h5pos
    have h25 : (5 : ℚ) * 5 = (25 : ℚ) := by norm_num
    rw [h25] at h
    rw [hf5] at h
    norm_num at h
    exact h
  have h11invpos : (1/11 : ℚ) > 0 := by norm_num
  have hf11inv : f (1/11 : ℚ) = -(11 : ℝ) := by
    have h := h₀ 11 h11pos (1/11) h11invpos
    have hprod : (11 : ℚ) * (1/11 : ℚ) = (1 : ℚ) := by norm_num
    rw [hprod] at h
    rw [hf11] at h
    rw [hf1] at h
    linarith
  have hf25over11 : f ((25 : ℚ) / 11) = (-1 : ℝ) := by
    rw [div_eq_mul_inv]
    have h := h₀ 25 h25pos (1/11) h11invpos
    rw [hf25, hf11inv] at h
    norm_num at h
    exact h
  rw [hf25over11]
  norm_num
