import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  rcases h₀ with ⟨hp, hp15⟩
  have hp_pos : 0 < p := hp
  have hp_lt_15 : p < 15 := hp15
  have hmem : 15 ∈ f '' Set.Icc p 15 := by
    refine ⟨15, ?_, ?_⟩
    · exact ⟨by linarith, by linarith⟩
    · rw [h₂ 15]
      have h1 : abs ((15 : ℝ) - p) = (15 : ℝ) - p := abs_of_nonneg (by linarith)
      have h2 : abs ((15 : ℝ) - (15 : ℝ)) = 0 := by simp
      have h3 : abs ((15 : ℝ) - p - (15 : ℝ)) = p := by
        calc
          abs ((15 : ℝ) - p - (15 : ℝ)) = abs (-p) := by ring
          _ = abs p := by simp
          _ = p := abs_of_pos hp
      rw [h1, h2, h3]
      linarith
  have hlower : ∀ b, b ∈ f '' Set.Icc p 15 → (15 : ℝ) ≤ b := by
    intro b hb
    rcases hb with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    rw [h₂ x]
    have hx_sub_p_nonneg : 0 ≤ x - p := by linarith
    have hx_sub_15_nonpos : x - (15 : ℝ) ≤ 0 := by linarith
    have hx_sub_p_sub_15_nonpos : x - p - (15 : ℝ) ≤ 0 := by linarith
    have habs1 : abs (x - p) = x - p := abs_of_nonneg hx_sub_p_nonneg
    have habs2 : abs (x - (15 : ℝ)) = -(x - (15 : ℝ)) := abs_of_nonpos hx_sub_15_nonpos
    have habs3 : abs (x - p - (15 : ℝ)) = -(x - p - (15 : ℝ)) := abs_of_nonpos hx_sub_p_sub_15_nonpos
    rw [habs1, habs2, habs3]
    linarith
  exact ⟨hmem, hlower⟩
