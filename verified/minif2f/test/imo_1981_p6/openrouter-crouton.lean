import Mathlib

open scoped Nat
open scoped Real

/--
The function $f(x,y)$ satisfies: $f(0,y)=y+1, f(x+1,0) = f(x,1), f(x+1,y+1)=f(x,f(x+1,y))$ for all non-negative integers $x,y$. Find $f(4,1981)$. -/
theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  have hf1 : ∀ y, f 1 y = y + 2 := by
    intro y
    induction y with
    | zero =>
      have h := h₁ 0
      simp [h₀] at h
      omega
    | succ y ih =>
      have h := h₂ 0 y
      simp [h₀] at h
      omega
  have hf2 : ∀ y, f 2 y = 2 * y + 3 := by
    intro y
    induction y with
    | zero =>
      have h := h₁ 1
      simp [hf1] at h
      omega
    | succ y ih =>
      have h := h₂ 1 y
      simp [hf1] at h
      omega
  have hf3 : ∀ y, f 3 y + 3 = 2 ^ (y + 3) := by
    intro y
    induction y with
    | zero =>
      have h := h₁ 2
      simp [hf2] at h
      rw [h]
      norm_num
    | succ y ih =>
      have h := h₂ 2 y
      simp [hf2] at h
      have hpow : (2 : ℕ) ^ (y + 1 + 3) = 2 * 2 ^ (y + 3) := by
        have e : y + 1 + 3 = (y + 3) + 1 := by ring
        rw [e, pow_succ]
        ring
      omega
  intro y
  have h := h₂ 3 y
  simp at h
  have h3 := hf3 (f 4 y)
  omega
