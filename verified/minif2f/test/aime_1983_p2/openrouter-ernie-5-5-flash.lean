import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  obtain ⟨hp_pos, hp_lt⟩ := h₀
  have key : ∀ x ∈ Set.Icc p 15, f x = 30 - x := by
    intro x hx
    rw [h₂ x]
    have hx1 : 0 ≤ x - p := by linarith [hx.1]
    have hx2 : x - 15 ≤ 0 := by linarith [hx.2]
    have hx3 : x - p - 15 ≤ 0 := by linarith [hx.2, hp_pos]
    rw [abs_of_nonneg hx1, abs_of_nonpos hx2, abs_of_nonpos hx3]
    ring
  refine ⟨⟨15, ⟨le_of_lt hp_lt, le_refl 15⟩, ?_⟩, ?_⟩
  · rw [key 15 ⟨le_of_lt hp_lt, le_refl 15⟩]
    norm_num
  · rintro y ⟨x, hx, rfl⟩
    rw [key x hx]
    linarith [hx.2]
