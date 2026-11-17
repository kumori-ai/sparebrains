import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  constructor
  · refine ⟨15, ?_, ?_⟩
    · exact ⟨le_of_lt h₀.2, le_rfl⟩
    · rw [h₂ 15]
      have hp : 0 ≤ p := le_of_lt h₀.1
      have h15p : 0 ≤ 15 - p := by linarith [h₀.2]
      have hneg : (15 : ℝ) - p - 15 = -p := by ring
      rw [show (15 : ℝ) - 15 = 0 by norm_num, hneg, abs_zero, abs_neg,
        abs_of_nonneg hp, abs_of_nonneg h15p]
      ring
  · rintro y ⟨x, hx, rfl⟩
    rw [h₂ x]
    have hxp : 0 ≤ x - p := by linarith [hx.1]
    have hx15 : x - 15 ≤ 0 := by linarith [hx.2]
    have hxp15 : x - p - 15 ≤ 0 := by linarith [hx.2, h₀.1]
    rw [abs_of_nonneg hxp, abs_of_nonpos hx15, abs_of_nonpos hxp15]
    linarith [hx.2]
