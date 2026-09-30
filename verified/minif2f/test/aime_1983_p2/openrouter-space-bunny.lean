import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  have hmem : ∀ x ∈ Set.Icc p 15, f x = 30 - x := by
    intro x hx
    rw [h₂ x]
    have hxp : 0 ≤ x - p := by linarith [hx.1]
    have hx15 : x - 15 ≤ 0 := by linarith [hx.2]
    have hxp15 : x - p - 15 ≤ 0 := by linarith [hx.2, h₀.1]
    rw [abs_of_nonneg hxp, abs_of_nonpos hx15, abs_of_nonpos hxp15]
    ring
  refine ⟨?_, ?_⟩
  · refine ⟨15, ⟨h₀.2.le, le_rfl⟩, ?_⟩
    rw [hmem 15 ⟨h₀.2.le, le_rfl⟩]
    ring
  · rintro y ⟨x, hx, rfl⟩
    rw [hmem x hx]
    linarith [hx.2]
