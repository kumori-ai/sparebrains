import Mathlib

open scoped Nat
open scoped Real

/--
If $a \star b = \dfrac{\left(\dfrac{1}{b} - \dfrac{1}{a}\right)}{(a - b)}$, express $3 \star 11$ as a common fraction. -/
theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ x ≠ 0, ∀ y ≠ 0, s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by
  rw [h₀ 3 (by norm_num) 11 (by norm_num)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring
