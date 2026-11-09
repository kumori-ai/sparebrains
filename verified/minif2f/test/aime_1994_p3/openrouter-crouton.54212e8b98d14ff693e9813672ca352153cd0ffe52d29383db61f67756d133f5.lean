import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ has the property that, for each real number $x,$ \[ f(x)+f(x-1) = x^2. \] If $f(19)=94,$ what is the remainder when $f(94)$ is divided by 1000? -/
theorem aime_1994_p3 (f : ℤ → ℤ) (h0 : ∀ x, f x + f (x - 1) = x ^ 2) (h1 : f 19 = 94) :
    f 94 % 1000 = 561 := by
  have hd : ∀ x : ℤ, f x - f (x - 2) = 2 * x - 1 := by
    intro x
    have h1' := h0 x
    have h2' := h0 (x - 1)
    have e1 : x - 1 - 1 = x - 2 := by ring
    rw [e1] at h2'
    have e2 : (x - 1) ^ 2 = x ^ 2 - 2 * x + 1 := by ring
    rw [e2] at h2'
    linarith
  have h20 : f 20 = 306 := by
    have h := h0 20
    have e : (20 : ℤ) - 1 = 19 := by norm_num
    rw [e, h1] at h
    norm_num at h
    linarith
  have hodd : ∀ k : ℕ, f (19 + 2 * (k : ℤ)) = 2 * (9 + (k : ℤ)) ^ 2 + 3 * (9 + (k : ℤ)) - 95 := by
    intro k
    induction k with
    | zero => simp [h1]
    | succ k ih =>
      have hd' := hd (21 + 2 * (k : ℤ))
      have e1 : (19 : ℤ) + 2 * ((k + 1 : ℕ) : ℤ) = 21 + 2 * (k : ℤ) := by push_cast; ring
      have e2 : (21 : ℤ) + 2 * (k : ℤ) - 2 = 19 + 2 * (k : ℤ) := by ring
      rw [e1]
      rw [e2] at hd'
      rw [ih] at hd'
      have hstep : f (21 + 2 * (k : ℤ)) =
          (2 * (9 + (k : ℤ)) ^ 2 + 3 * (9 + (k : ℤ)) - 95) + (2 * (21 + 2 * (k : ℤ)) - 1) := by
        linarith
      rw [hstep]
      push_cast
      ring
  have heven : ∀ k : ℕ, f (20 + 2 * (k : ℤ)) = 2 * (10 + (k : ℤ)) ^ 2 + (10 + (k : ℤ)) + 96 := by
    intro k
    induction k with
    | zero => simp [h20]
    | succ k ih =>
      have hd' := hd (22 + 2 * (k : ℤ))
      have e1 : (20 : ℤ) + 2 * ((k + 1 : ℕ) : ℤ) = 22 + 2 * (k : ℤ) := by push_cast; ring
      have e2 : (22 : ℤ) + 2 * (k : ℤ) - 2 = 20 + 2 * (k : ℤ) := by ring
      rw [e1]
      rw [e2] at hd'
      rw [ih] at hd'
      have hstep : f (22 + 2 * (k : ℤ)) =
          (2 * (10 + (k : ℤ)) ^ 2 + (10 + (k : ℤ)) + 96) + (2 * (22 + 2 * (k : ℤ)) - 1) := by
        linarith
      rw [hstep]
      push_cast
      ring
  have h94 : f 94 = 4561 := by
    have h := heven 37
    have e : (20 : ℤ) + 2 * ((37 : ℕ) : ℤ) = 94 := by norm_num
    rw [e] at h
    norm_num at h
    exact h
  rw [h94]
  norm_num
