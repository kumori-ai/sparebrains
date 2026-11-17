import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = 12x+7$ and $g(x) = 5x+2$ whenever $x$ is a positive integer. Define $h(x)$ to be the greatest common divisor of $f(x)$ and $g(x)$. What is the sum of all possible values of $h(x)$? -/
theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
    (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
    ∑ k ∈ (Set.range h).toFinset, k = 12 := by
  have h_cases : ∀ x : ℕ+, h x = 1 ∨ h x = 11 := by
    intro x
    have hdvd1 : h x ∣ 12 * (x : ℕ) + 7 := by
      rw [h₂ x, h₀ x, h₁ x]
      exact Nat.gcd_dvd_left _ _
    have hdvd2 : h x ∣ 5 * (x : ℕ) + 2 := by
      rw [h₂ x, h₀ x, h₁ x]
      exact Nat.gcd_dvd_right _ _
    have h1 : h x ∣ 5 * (12 * (x : ℕ) + 7) := dvd_mul_of_dvd_right hdvd1 5
    have h2 : h x ∣ 12 * (5 * (x : ℕ) + 2) := dvd_mul_of_dvd_right hdvd2 12
    have heq : 5 * (12 * (x : ℕ) + 7) = 12 * (5 * (x : ℕ) + 2) + 11 := by ring
    rw [heq] at h1
    have hdvd11 : h x ∣ 11 := (Nat.dvd_add_right h2).mp h1
    have hp : Nat.Prime 11 := by norm_num
    exact (Nat.dvd_prime hp).mp hdvd11
  have h1val : h 1 = 1 := by
    norm_num [h₂, h₀, h₁]
  have h4val : h 4 = 11 := by
    norm_num [h₂, h₀, h₁]
  have hrange : Set.range h = ({1, 11} : Set ℕ) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simpa using h_cases x
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, h1val⟩
      · exact ⟨4, h4val⟩
  have hfin : (Set.range h).toFinset = ({1, 11} : Finset ℕ) := by
    ext y
    simp [hrange]
  rw [hfin]
  simp
