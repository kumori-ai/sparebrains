import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ has the property that, for each real number $x,$ \[ f(x)+f(x-1) = x^2. \] If $f(19)=94,$ what is the remainder when $f(94)$ is divided by 1000? -/
theorem aime_1994_p3 (f : ℤ → ℤ) (h0 : ∀ x, f x + f (x - 1) = x ^ 2) (h1 : f 19 = 94) :
    f 94 % 1000 = 561 := by
  have step : ∀ n : ℤ, f n = f (n - 2) + (2 * n - 1) := by
    intro n
    have ha := h0 n
    have hb := h0 (n - 1)
    have hsub : (n - 1) - 1 = n - 2 := by ring
    rw [hsub] at hb
    have hdiff : f n = f (n - 2) + (n ^ 2 - (n - 1) ^ 2) := by linarith
    rw [hdiff]
    congr 1
    ring
  have h20 : f 20 = 306 := by
    have ha := h0 20
    norm_num at ha
    linarith
  have key : ∀ k : ℕ, f (20 + 2 * (k : ℤ)) = 306 + 39 * (k : ℤ) + 2 * (k : ℤ) * ((k : ℤ) + 1) := by
    intro k
    induction k with
    | zero => simp [h20]
    | succ k ih =>
      push_cast
      have hstep := step (20 + 2 * ((k : ℤ) + 1))
      have harg : (20 + 2 * ((k : ℤ) + 1)) - 2 = 20 + 2 * (k : ℤ) := by ring
      rw [harg] at hstep
      rw [hstep, ih]
      ring
  have h94 : f 94 = 4561 := by
    have h := key 37
    norm_num at h
    exact h
  rw [h94]
  norm_num
