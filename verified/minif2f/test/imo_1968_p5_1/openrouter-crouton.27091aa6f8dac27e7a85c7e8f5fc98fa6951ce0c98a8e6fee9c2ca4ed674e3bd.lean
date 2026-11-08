import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have hge : ∀ x, 1 / 2 ≤ f x := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    have hs : 0 ≤ Real.sqrt (f (x - a) - f (x - a) ^ 2) := Real.sqrt_nonneg _
    linarith
  have hle : ∀ x, f x ≤ 1 := by
    intro x
    have h := h₁ (x - a)
    rw [sub_add_cancel] at h
    rw [h]
    have harg : f (x - a) - f (x - a) ^ 2 ≤ 1 / 4 := by
      have e : f (x - a) - f (x - a) ^ 2 = 1 / 4 - (f (x - a) - 1 / 2) ^ 2 := by ring
      rw [e]
      have hs : 0 ≤ (f (x - a) - 1 / 2) ^ 2 := sq_nonneg _
      linarith
    have hsqrt : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ 1 / 2 := by
      have h1 : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ Real.sqrt (1 / 4) :=
        Real.sqrt_le_sqrt harg
      have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [h2] at h1
      exact h1
    linarith
  have hnonneg : ∀ x, 0 ≤ f x - f x ^ 2 := by
    intro x
    have e : f x - f x ^ 2 = f x * (1 - f x) := by ring
    rw [e]
    apply mul_nonneg
    · linarith [hge x]
    · linarith [hle x]
  have hsq : ∀ x, (f (x + a) - 1 / 2) ^ 2 = f x - f x ^ 2 := by
    intro x
    have h := h₁ x
    have e : f (x + a) - 1 / 2 = Real.sqrt (f x - f x ^ 2) := by linarith
    rw [e, Real.sq_sqrt (hnonneg x)]
  refine ⟨2 * a, by linarith, ?_⟩
  intro x
  have h_eq : x + 2 * a = (x + a) + a := by ring
  rw [h_eq, h₁ (x + a)]
  have hinside : f (x + a) - f (x + a) ^ 2 = (f x - 1 / 2) ^ 2 := by
    have e1 : f (x + a) - f (x + a) ^ 2 = 1 / 4 - (f (x + a) - 1 / 2) ^ 2 := by ring
    rw [e1, hsq x]
    ring
  rw [hinside, Real.sqrt_sq (by linarith [hge x])]
  ring
