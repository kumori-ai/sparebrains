import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  obtain ⟨hp0, hp15⟩ := h₀
  constructor
  · refine ⟨15, ⟨le_of_lt hp15, le_rfl⟩, ?_⟩
    rw [h₂ 15]
    have h1 : (0 : ℝ) ≤ 15 - p := by linarith
    have h2abs : abs ((15 : ℝ) - 15) = 0 := by simp
    have h3 : abs (15 - p - 15) = p := by
      have he : (15 : ℝ) - p - 15 = -p := by ring
      rw [he, abs_neg, abs_of_nonneg (le_of_lt hp0)]
    rw [abs_of_nonneg h1, h2abs, h3]
    linarith
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [h₂ x]
    have hx1 : p ≤ x := hx.1
    have hx2 : x ≤ 15 := hx.2
    have a1 : abs (x - p) = x - p := abs_of_nonneg (by linarith)
    have hle2 : x - 15 ≤ 0 := by linarith
    have a2 : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos hle2]
      ring
    have hle3 : x - p - 15 ≤ 0 := by linarith
    have a3 : abs (x - p - 15) = p + 15 - x := by
      rw [abs_of_nonpos hle3]
      ring
    rw [a1, a2, a3]
    linarith
