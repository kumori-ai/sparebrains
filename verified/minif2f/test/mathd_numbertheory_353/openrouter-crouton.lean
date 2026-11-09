import Mathlib

open scoped Nat
open scoped Real

/-- Let $S = 2010 + 2011 + \cdots + 4018$. Compute the residue of $S$, modulo 2009. -/
theorem mathd_numbertheory_353 (s : ℕ) (h₀ : s = ∑ k ∈ Finset.Icc 2010 4018, k) : s % 2009 = 0 := by
  have hIcc : Finset.Icc 2010 4018 = (Finset.range 2009).image (fun i => 2010 + i) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨x - 2010, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hs : s = ∑ i ∈ Finset.range 2009, (2010 + i) := by
    rw [h₀, hIcc, Finset.sum_image (by intro x _ y _ h; dsimp at h; omega)]
  have h1 : ∑ i ∈ Finset.range 2009, i = 2009 * 1004 := by
    rw [Finset.sum_range_id]
  have h2 : ∑ _i ∈ Finset.range 2009, 2010 = 2009 * 2010 := by
    simp [Finset.sum_const]
  have hs2 : s = 2009 * 3014 := by
    rw [hs, Finset.sum_add_distrib, h1, h2]
  rw [hs2]
