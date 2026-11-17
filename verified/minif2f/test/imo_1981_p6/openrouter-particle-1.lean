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
        calc
          f 1 0 = f 0 1 := by simpa using h₁ 0
          _ = 1 + 1 := h₀ 1
          _ = 0 + 2 := by norm_num
    | succ y ih =>
        calc
          f 1 (y + 1) = f 0 (f 1 y) := by simpa using h₂ 0 y
          _ = f 1 y + 1 := h₀ (f 1 y)
          _ = (y + 2) + 1 := by rw [ih]
          _ = (y + 1) + 2 := by omega
  have hf2 : ∀ y, f 2 y = 2 * y + 3 := by
    intro y
    induction y with
    | zero =>
        calc
          f 2 0 = f 1 1 := by simpa using h₁ 1
          _ = 1 + 2 := hf1 1
          _ = 2 * 0 + 3 := by norm_num
    | succ y ih =>
        calc
          f 2 (y + 1) = f 1 (f 2 y) := by simpa using h₂ 1 y
          _ = f 2 y + 2 := hf1 (f 2 y)
          _ = (2 * y + 3) + 2 := by rw [ih]
          _ = 2 * (y + 1) + 3 := by omega
  have hf3 : ∀ y, f 3 y + 3 = 2 ^ (y + 3) := by
    intro y
    induction y with
    | zero =>
        calc
          f 3 0 + 3 = f 2 1 + 3 := by rw [show f 3 0 = f 2 1 by simpa using h₁ 2]
          _ = (2 * 1 + 3) + 3 := by rw [hf2 1]
          _ = 2 ^ (0 + 3) := by norm_num
    | succ y ih =>
        calc
          f 3 (y + 1) + 3 = f 2 (f 3 y) + 3 := by rw [show f 3 (y + 1) = f 2 (f 3 y) by simpa using h₂ 2 y]
          _ = (2 * f 3 y + 3) + 3 := by rw [hf2]
          _ = 2 * (f 3 y + 3) := by ring
          _ = 2 * 2 ^ (y + 3) := by rw [ih]
          _ = 2 ^ (y + 1 + 3) := by
            rw [show y + 1 + 3 = (y + 3) + 1 by omega]
            rw [pow_succ]
            ring
  have hf3_sub : ∀ y, f 3 y = 2 ^ (y + 3) - 3 := by
    intro y
    have h := hf3 y
    rw [← h]
    rw [Nat.add_sub_cancel]
  intro y
  calc
    f 4 (y + 1) = f 3 (f 4 y) := by simpa using h₂ 3 y
    _ = 2 ^ (f 4 y + 3) - 3 := hf3_sub (f 4 y)
