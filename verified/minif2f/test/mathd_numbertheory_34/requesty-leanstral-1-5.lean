import Mathlib

open scoped Nat
open scoped Real

/--
Find $9^{-1} \pmod{100}$, as a residue modulo 100.  (Give an answer between 0 and 99, inclusive.) -/
theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by
  have hx : x ∈ Finset.range 100 := Finset.mem_range.mpr h₀
  have h_all : (Finset.filter (λ x => x * 9 % 100 = 1) (Finset.range 100)) = {89} := by
    decide
  have hx_filter : x ∈ Finset.filter (λ x => x * 9 % 100 = 1) (Finset.range 100) := by
    apply Finset.mem_filter.mpr
    exact ⟨hx, h₁⟩
  rw [h_all] at hx_filter
  simpa using hx_filter
