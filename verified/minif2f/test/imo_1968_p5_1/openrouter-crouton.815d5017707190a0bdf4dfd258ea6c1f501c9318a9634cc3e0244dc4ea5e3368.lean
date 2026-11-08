import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have hrange : ∀ t, 1 / 2 ≤ f t ∧ f t ≤ 1 := by
    intro t
    have ht : f t = 1 / 2 + Real.sqrt (f (t - a) - f (t - a) ^ 2) := by
      have h := h₁ (t - a)
      rwa [sub_add_cancel] at h
    constructor
    · rw [ht]
      have hnn := Real.sqrt_nonneg (f (t - a) - f (t - a) ^ 2)
      linarith
    · rw [ht]
      have hle : Real.sqrt (f (t - a) - f (t - a) ^ 2) ≤ 1 / 2 := by
        have h14 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [← h14]
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (f (t - a) - 1 / 2)]
      linarith
  refine ⟨2 * a, by linarith, ?_⟩
  intro x
  have hy := hrange x
  have h1 := h₁ x
  have h2 := h₁ (x + a)
  have hx2 : x + 2 * a = (x + a) + a := by ring
  rw [hx2, h2, h1]
  set s := Real.sqrt (f x - f x ^ 2) with hs
  have hnn : 0 ≤ f x - f x ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ f x by linarith) (show (0 : ℝ) ≤ 1 - f x by linarith)]
  have hs_sq : s ^ 2 = f x - f x ^ 2 := by
    rw [hs]
    exact Real.sq_sqrt hnn
  have harg : (1 / 2 + s) - (1 / 2 + s) ^ 2 = (f x - 1 / 2) ^ 2 := by
    have h : (1 / 2 + s) - (1 / 2 + s) ^ 2 = 1 / 4 - s ^ 2 := by ring
    rw [h, hs_sq]
    ring
  rw [harg]
  have hsqrt : Real.sqrt ((f x - 1 / 2) ^ 2) = f x - 1 / 2 :=
    Real.sqrt_sq (by linarith [hy.1])
  rw [hsqrt]
  ring
