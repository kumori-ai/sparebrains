import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have h_ge_half : ∀ x, 1/2 ≤ f x := by
    intro x
    have hx : f x = 1/2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
      calc
        f x = f ((x - a) + a) := by ring
        _ = 1/2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := h₁ (x - a)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (f (x - a) - f (x - a) ^ 2) := Real.sqrt_nonneg _
    linarith
  have h_le_one : ∀ x, f x ≤ 1 := by
    intro x
    have hx : f x = 1/2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := by
      calc
        f x = f ((x - a) + a) := by ring
        _ = 1/2 + Real.sqrt (f (x - a) - f (x - a) ^ 2) := h₁ (x - a)
    have h_sq_le : f (x - a) - f (x - a) ^ 2 ≤ 1/4 := by
      have h_sq_nonneg : 0 ≤ (f (x - a) - 1/2)^2 := sq_nonneg _
      nlinarith
    have h_sqrt_le : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ 1/2 := by
      calc
        Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ Real.sqrt (1/4) := Real.sqrt_le_sqrt h_sq_le
        _ = 1/2 := by norm_num
    linarith
  have h_nonneg : ∀ x, 0 ≤ f x - f x ^ 2 := by
    intro x
    have hx := h_ge_half x
    have hy := h_le_one x
    nlinarith
  have h_period : ∀ x, f (x + 2*a) = f x := by
    intro x
    have hfxpa : f (x + a) = 1/2 + Real.sqrt (f x - f x ^ 2) := h₁ x
    have h_sq_sqrt : (Real.sqrt (f x - f x ^ 2)) ^ 2 = f x - f x ^ 2 := Real.sq_sqrt (h_nonneg x)
    have h_expr : f (x + a) - f (x + a) ^ 2 = (f x - 1/2)^2 := by
      calc
        f (x + a) - f (x + a) ^ 2 = (1/2 + Real.sqrt (f x - f x ^ 2)) - (1/2 + Real.sqrt (f x - f x ^ 2)) ^ 2 := by rw [hfxpa]
        _ = 1/4 - (Real.sqrt (f x - f x ^ 2)) ^ 2 := by ring
        _ = 1/4 - (f x - f x ^ 2) := by rw [h_sq_sqrt]
        _ = (f x - 1/2)^2 := by ring
    calc
      f (x + 2*a) = f ((x + a) + a) := by ring
      _ = 1/2 + Real.sqrt (f (x + a) - f (x + a) ^ 2) := h₁ (x + a)
      _ = 1/2 + Real.sqrt ((f x - 1/2)^2) := by rw [h_expr]
      _ = 1/2 + |f x - 1/2| := by rw [Real.sqrt_sq_eq_abs]
      _ = 1/2 + (f x - 1/2) := by rw [abs_of_nonneg (sub_nonneg.mpr (h_ge_half x))]
      _ = f x := by ring
  refine ⟨2*a, by linarith, h_period⟩
