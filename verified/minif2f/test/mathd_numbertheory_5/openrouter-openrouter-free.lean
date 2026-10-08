import Mathlib

open scoped Nat
open scoped Real

/--
What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? -/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  have h_eq : x ^ 2 = t ^ 3 := by
    calc
      x ^ 2 = n := hx
      _ = t ^ 3 := ht.symm
  have h_coprime : (2 : ℕ) ≠ 0 ∨ (3 : ℕ) ≠ 0 := by
    exact Or.inl (by decide)
  obtain ⟨c, hxc, htc⟩ := Nat.exists_eq_pow_of_pow_eq_pow h_coprime h_eq
  have hn : n = c ^ 6 := by
    have h1 : n = x ^ 2 := by linarith
    have h2 : x = c ^ 3 := hxc
    rw [h1, h2]
    have h3 : (c ^ 3 : ℕ) ^ 2 = c ^ 6 := by
      ring
      <;> simp [pow_mul]
      <;> ring
    rw [h3]
    <;> norm_num
  have hc : c ≥ 2 := by
    by_contra h
    have h₁ : c ≤ 1 := by linarith
    interval_cases c <;> norm_num at h₀ ⊢ <;>
      (try omega) <;>
      (try
        {
          have h₂ : n = c ^ 6 := hn
          rw [h₂] at *
          <;> norm_num at * <;> omega
        })
  have h_final : 64 ≤ n := by
    have h₁ : n = c ^ 6 := hn
    rw [h₁]
    have h₂ : c ≥ 2 := hc
    have h₃ : c ^ 2 ≥ 4 := by
      nlinarith
    have h₄ : c ^ 3 ≥ 8 := by
      have h₄₁ : c ^ 3 = c ^ 2 * c := by ring
      rw [h₄₁]
      have h₄₂ : c ^ 2 ≥ 4 := h₃
      have h₄₃ : c ≥ 2 := h₂
      nlinarith
    have h₅ : c ^ 6 ≥ 64 := by
      have h₅₁ : c ^ 6 = (c ^ 3) ^ 2 := by ring
      rw [h₅₁]
      have h₅₂ : c ^ 3 ≥ 8 := h₄
      have h₅₃ : c ^ 3 ≥ 0 := by positivity
      nlinarith
    exact h₅
  exact h_final
