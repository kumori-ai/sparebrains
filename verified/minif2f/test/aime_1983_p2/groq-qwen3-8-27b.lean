import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = |x - p| + |x - 15| + |x - p - 15|$, where $0 < p < 15$.  Determine the minimum value taken by $f(x)$ for $x$ in the interval $p \le x \le 15$. -/
theorem aime_1983_p2 (p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15)
    (h₂ : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : IsLeast (f '' Set.Icc p 15) 15 := by
  have h₁ : 0 < p := h₀.1
  have h₂' : p < 15 := h₀.2
  have h_mem : 15 ∈ f '' Set.Icc p 15 := by
    have h15 : (15 : ℝ) ∈ Set.Icc p 15 := by
      constructor
      · linarith
      · linarith
    have hf15 : f (15 : ℝ) = 15 := by
      rw [h₂]
      have h_abs1 : abs ((15 : ℝ) - p) = (15 : ℝ) - p := by
        rw [abs_of_nonneg]
        linarith
      have h_abs2 : abs ((15 : ℝ) - (15 : ℝ)) = 0 := by
        norm_num
      have h_abs3 : abs ((15 : ℝ) - p - (15 : ℝ)) = p := by
        have h_neg : (15 : ℝ) - p - 15 = -p := by ring
        rw [h_neg]
        rw [abs_of_nonpos]
        · linarith
        · linarith
      rw [h_abs1, h_abs2, h_abs3]
      ring
    exact ⟨15, h15, hf15⟩
  have h_least : ∀ y ∈ f '' Set.Icc p 15, 15 ≤ y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 : p ≤ x := hx.1
    have hx2 : x ≤ 15 := hx.2
    have h_abs1 : abs (x - p) = x - p := by
      rw [abs_of_nonneg]
      linarith
    have h_abs2 : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have h_abs3 : abs (x - p - 15) = p + 15 - x := by
      have h_nonpos : x - p - 15 ≤ 0 := by
        linarith
      rw [abs_of_nonpos h_nonpos]
      ring
    rw [h₂, h_abs1, h_abs2, h_abs3]
    have h_simp : (x - p) + (15 - x) + (p + 15 - x) = 30 - x := by ring
    rw [h_simp]
    linarith
  exact ⟨h_mem, h_least⟩
