import Mathlib

open scoped Nat
open scoped Real

/--
The function $f(x,y)$ satisfies: $f(0,y)=y+1, f(x+1,0) = f(x,1), f(x+1,y+1)=f(x,f(x+1,y))$ for all non-negative integers $x,y$. Find $f(4,1981)$. -/
theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 := by
  have f1_eq : ∀ x, f 1 x = x + 2 := by
    intro x
    induction x with
    | zero =>
      rw [h₁ 0, h₀ 1]
    | succ x ih =>
      rw [h₂ 0 x, h₀ (f 1 x), ih]
  have f2_eq : ∀ x, f 2 x = 2*x + 3 := by
    intro x
    induction x with
    | zero =>
      rw [h₁ 1, f1_eq 1]
    | succ x ih =>
      rw [h₂ 1 x, f1_eq (f 2 x), ih]
      omega
  have f3_eq_add : ∀ x, f 3 x + 3 = 2^(x+3) := by
    intro x
    induction x with
    | zero =>
      rw [h₁ 2, f2_eq 1]
      norm_num
    | succ x ih =>
      rw [h₂ 2 x, f2_eq (f 3 x)]
      calc
        (2 * f 3 x + 3) + 3 = 2 * f 3 x + 6 := by omega
        _ = 2 * (f 3 x + 3) := by omega
        _ = 2 * (2^(x+3)) := by rw [ih]
        _ = 2^(x+4) := by
          exact Eq.symm Nat.pow_succ'
  have f3_eq : ∀ x, f 3 x = 2^(x+3) - 3 := by
    intro x
    exact Nat.eq_sub_of_add_eq (f3_eq_add x)
  intro y
  aesop