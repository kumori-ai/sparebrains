import Mathlib

open scoped Nat
open scoped Real

/--
Let $f$ be a real-valued function defined for all real numbers, such that for some $a>0$ we have \[ f(x+a)={1\over2}+\sqrt{f(x)-f(x)^2} \] for all $x$.
Prove that $f$ is periodic, and give an example of such a non-constant $f$ for $a=1$. -/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  have h_lower : ∀ x : ℝ, (1 : ℝ) / 2 ≤ f x := by
    intro x
    have h := h₁ (x - a)
    have hx : x - a + a = x := by ring
    rw [hx] at h
    rw [h]
    have hs : 0 ≤ Real.sqrt (f (x - a) - f (x - a) ^ 2) := Real.sqrt_nonneg _
    linarith

  have sqrt_le_half : ∀ y : ℝ, Real.sqrt (y - y ^ 2) ≤ (1 : ℝ) / 2 := by
    intro y
    by_cases hnon : 0 ≤ y - y ^ 2
    · have hle : y - y ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
        nlinarith [sq_nonneg (y - (1 : ℝ) / 2)]
      calc
        Real.sqrt (y - y ^ 2) ≤ Real.sqrt (((1 : ℝ) / 2) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (1 : ℝ) / 2 := by
          rw [Real.sqrt_sq_eq_abs]
          norm_num
    · have hzero : Real.sqrt (y - y ^ 2) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hnon)
      rw [hzero]
      norm_num

  have h_upper : ∀ x : ℝ, f x ≤ 1 := by
    intro x
    have h := h₁ (x - a)
    have hx : x - a + a = x := by ring
    rw [hx] at h
    rw [h]
    have hs : Real.sqrt (f (x - a) - f (x - a) ^ 2) ≤ (1 : ℝ) / 2 :=
      sqrt_le_half (f (x - a))
    linarith

  use 2 * a
  constructor
  · linarith
  · intro x
    have hnon : 0 ≤ f x - f x ^ 2 := by
      have h1 : 0 ≤ f x := by linarith [h_lower x]
      have h2 : 0 ≤ 1 - f x := by linarith [h_upper x]
      have hmul : 0 ≤ f x * (1 - f x) := mul_nonneg h1 h2
      nlinarith
    set s : ℝ := Real.sqrt (f x - f x ^ 2) with hs_def
    have hs_sq : s ^ 2 = f x - f x ^ 2 := by
      rw [hs_def]
      exact Real.sq_sqrt hnon
    have hfa : f (x + a) = (1 : ℝ) / 2 + s := by
      rw [h₁ x, hs_def]
    have hrad : ((1 : ℝ) / 2 + s) - ((1 : ℝ) / 2 + s) ^ 2 =
        (f x - (1 : ℝ) / 2) ^ 2 := by
      calc
        ((1 : ℝ) / 2 + s) - ((1 : ℝ) / 2 + s) ^ 2 = (1 : ℝ) / 4 - s ^ 2 := by ring
        _ = (1 : ℝ) / 4 - (f x - f x ^ 2) := by rw [hs_sq]
        _ = (f x - (1 : ℝ) / 2) ^ 2 := by ring
    have hsqrt : Real.sqrt (((1 : ℝ) / 2 + s) - ((1 : ℝ) / 2 + s) ^ 2) =
        f x - (1 : ℝ) / 2 := by
      rw [hrad]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by linarith [h_lower x])]
    have hx2 : x + 2 * a = (x + a) + a := by ring
    rw [hx2, h₁ (x + a), hfa, hsqrt]
    ring
