import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have hpos : ∀ x, f x ≥ 1/2 := by
    intro x
    have h := h₁ (x - a)
    have hx : f x = 1/2 + Real.sqrt (f (x - a) - (f (x - a)) ^ 2) := by
      calc
        f x = f ((x - a) + a) := by ring
        _ = 1/2 + Real.sqrt (f (x - a) - (f (x - a)) ^ 2) := h₁ (x - a)
    rw [hx]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (f (x - a) - (f (x - a)) ^ 2) := Real.sqrt_nonneg _
    linarith
  have hle1 : ∀ x, f x ≤ 1 := by
    intro x
    have hbound : ∀ y : ℝ, y - y ^ 2 ≤ 1/4 := by
      intro y
      have hsq : (y - 1/2)^2 ≥ 0 := by nlinarith
      nlinarith
    have h := h₁ (x - a)
    have hx : f x = 1/2 + Real.sqrt (f (x - a) - (f (x - a)) ^ 2) := by
      calc
        f x = f ((x - a) + a) := by ring
        _ = 1/2 + Real.sqrt (f (x - a) - (f (x - a)) ^ 2) := h₁ (x - a)
    rw [hx]
    have hsqrt_le : Real.sqrt (f (x - a) - (f (x - a)) ^ 2) ≤ Real.sqrt (1/4) :=
      Real.sqrt_le_sqrt (hbound (f (x - a)))
    have hsqrt_quarter : Real.sqrt (1/4 : ℝ) = 1/2 := by norm_num
    rw [hsqrt_quarter] at hsqrt_le
    linarith
  have h_period : ∀ x, f (x + 2*a) = f x := by
    intro x
    have hy_nonneg : 0 ≤ f x - (f x)^2 := by
      have hx1 := hpos x
      have hx2 := hle1 x
      nlinarith
    have hfx := h₁ x
    have hcalc : f (x + a) - (f (x + a)) ^ 2 = (f x - 1/2)^2 := by
      rw [hfx]
      have hs_sq : (Real.sqrt (f x - (f x)^2))^2 = f x - (f x)^2 := Real.sq_sqrt hy_nonneg
      calc
        (1/2 + Real.sqrt (f x - (f x)^2)) - (1/2 + Real.sqrt (f x - (f x)^2))^2
            = (1/2 + Real.sqrt (f x - (f x)^2)) - ((1/2)^2 + 2*(1/2)*Real.sqrt (f x - (f x)^2) + (Real.sqrt (f x - (f x)^2))^2) := by ring
        _ = (1/2 + Real.sqrt (f x - (f x)^2)) - (1/4 + Real.sqrt (f x - (f x)^2) + (Real.sqrt (f x - (f x)^2))^2) := by ring
        _ = 1/4 - (Real.sqrt (f x - (f x)^2))^2 := by ring
        _ = 1/4 - (f x - (f x)^2) := by rw [hs_sq]
        _ = (f x - 1/2)^2 := by ring
    calc
      f (x + 2*a) = f ((x + a) + a) := by ring
      _ = 1/2 + Real.sqrt (f (x + a) - (f (x + a)) ^ 2) := h₁ (x + a)
      _ = 1/2 + Real.sqrt ((f x - 1/2)^2) := by rw [hcalc]
      _ = 1/2 + (f x - 1/2) := by
        rw [Real.sqrt_sq (sub_nonneg.mpr (hpos x))]
      _ = f x := by ring
  refine ⟨2*a, by nlinarith, h_period⟩
