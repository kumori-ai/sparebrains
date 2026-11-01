import Mathlib

open scoped Nat
open scoped Real

/--
Find $9^{-1} \pmod{100}$, as a residue modulo 100.  (Give an answer between 0 and 99, inclusive.) -/
theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by
  have h_all : (Finset.range 100).filter (λ x => x * 9 % 100 = 1) = {89} := by
    decide
  have hx_mem : x ∈ Finset.range 100 := Finset.mem_range.mpr h₀
  have hx_filter : x ∈ (Finset.range 100).filter (λ x => x * 9 % 100 = 1) := by
    apply Finset.mem_filter.mpr
    exact ⟨hx_mem, h₁⟩
  rw [h_all] at hx_filter
  simpa using hx_filter
