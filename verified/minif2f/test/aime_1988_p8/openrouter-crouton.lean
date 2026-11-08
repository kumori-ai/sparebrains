import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$, defined on the set of ordered pairs of positive integers, satisfies the following properties:
\begin{eqnarray*} f(x,x) &=& x, \\ f(x,y) &=& f(y,x), \quad \text{and} \\ (x + y) f(x,y) &=& yf(x,x + y). \end{eqnarray*}
Calculate $f(14,52)$. -/
theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by
  have step_lt : ∀ x y : ℕ, 0 < x → x < y →
      ((y - x : ℕ) : ℝ) * f x y = (y : ℝ) * f x (y - x) := by
    intro x y hx hxy
    have hpos : 0 < y - x := by omega
    have h := h₂ x (y - x) ⟨hx, hpos⟩
    have hsum : x + (y - x) = y := by omega
    rw [hsum] at h
    have hcast : (x : ℝ) + ((y - x : ℕ) : ℝ) = (y : ℝ) := by
      rw [← Nat.cast_add, hsum]
    rw [hcast] at h
    exact h.symm
  have step_gt : ∀ x y : ℕ, 0 < y → y < x →
      ((x - y : ℕ) : ℝ) * f x y = (x : ℝ) * f (x - y) y := by
    intro x y hy hyx
    have hpos : 0 < x - y := by omega
    have h := h₂ y (x - y) ⟨hy, hpos⟩
    have hsum : y + (x - y) = x := by omega
    rw [hsum] at h
    have hcast : (y : ℝ) + ((x - y : ℕ) : ℝ) = (x : ℝ) := by
      rw [← Nat.cast_add, hsum]
    rw [hcast] at h
    have hs1 : f y (x - y) = f (x - y) y := h₁ y (x - y) ⟨hy, hpos⟩
    have hs2 : f y x = f x y := h₁ y x ⟨hy, by omega⟩
    rw [hs1, hs2] at h
    exact h.symm
  have s1 := step_lt 14 52 (by norm_num) (by norm_num)
  have s2 := step_lt 14 38 (by norm_num) (by norm_num)
  have s3 := step_lt 14 24 (by norm_num) (by norm_num)
  have s4 := step_gt 14 10 (by norm_num) (by norm_num)
  have s5 := step_lt 4 10 (by norm_num) (by norm_num)
  have s6 := step_lt 4 6 (by norm_num) (by norm_num)
  have s7 := step_gt 4 2 (by norm_num) (by norm_num)
  have h22 := h₀ 2 (by norm_num)
  norm_num at s1 s2 s3 s4 s5 s6 s7 h22
  linarith
