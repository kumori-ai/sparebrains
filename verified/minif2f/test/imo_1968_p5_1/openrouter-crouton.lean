import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have hbound : ∀ t, 1 / 2 ≤ f t ∧ f t ≤ 1 := by
    intro t
    have h := h₁ (t - a)
    rw [sub_add_cancel] at h
    constructor
    · rw [h]
      linarith [Real.sqrt_nonneg (f (t - a) - f (t - a) ^ 2)]
    · rw [h]
      have hle : f (t - a) - f (t - a) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_nonneg (f (t - a) - 1 / 2)]
      have hsqrt : Real.sqrt (f (t - a) - f (t - a) ^ 2) ≤ 1 / 2 := by
        have h14 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [← h14]
        exact Real.sqrt_le_sqrt hle
      linarith
  refine ⟨2 * a, by linarith, ?_⟩
  intro x
  have hx := hbound x
  have h1 := h₁ x
  have h2 := h₁ (x + a)
  have h2' : f (x + 2 * a) = 1 / 2 + Real.sqrt (f (x + a) - f (x + a) ^ 2) := by
    rw [show x + 2 * a = (x + a) + a by ring]
    exact h2
  rw [h2', h1]
  set u := f x with hu
  set s := Real.sqrt (u - u ^ 2) with hs
  have hnn : 0 ≤ u - u ^ 2 := by
    have hprod : 0 ≤ u * (1 - u) :=
      mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    nlinarith [hprod]
  have hs2 : s ^ 2 = u - u ^ 2 := Real.sq_sqrt hnn
  have hcalc : (1 / 2 + s) - (1 / 2 + s) ^ 2 = (u - 1 / 2) ^ 2 := by
    have htmp : (1 / 2 + s) - (1 / 2 + s) ^ 2 = 1 / 4 - s ^ 2 := by ring
    rw [htmp, hs2]
    ring
  rw [hcalc]
  have hsqrt2 : Real.sqrt ((u - 1 / 2) ^ 2) = u - 1 / 2 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [hx.1])]
  rw [hsqrt2]
  ring
