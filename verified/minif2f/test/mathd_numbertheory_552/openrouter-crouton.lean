import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = 12x+7$ and $g(x) = 5x+2$ whenever $x$ is a positive integer. Define $h(x)$ to be the greatest common divisor of $f(x)$ and $g(x)$. What is the sum of all possible values of $h(x)$? -/
theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
    (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
    ∑ k ∈ (Set.range h).toFinset, k = 12 := by
  have hrange : Set.range h = {1, 11} := by
    ext k
    constructor
    · rintro ⟨x, rfl⟩
      have hdvd : h x ∣ 11 := by
        have h1 : h x ∣ f x := by
          rw [h₂]
          exact Nat.gcd_dvd_left _ _
        have h2 : h x ∣ g x := by
          rw [h₂]
          exact Nat.gcd_dvd_right _ _
        have h3 : h x ∣ f x * 5 := dvd_mul_of_dvd_left h1 5
        have h4 : h x ∣ g x * 12 := dvd_mul_of_dvd_left h2 12
        have h3i : (h x : ℤ) ∣ (f x : ℤ) * 5 := by exact_mod_cast h3
        have h4i : (h x : ℤ) ∣ (g x : ℤ) * 12 := by exact_mod_cast h4
        have h5i : (h x : ℤ) ∣ (f x : ℤ) * 5 - (g x : ℤ) * 12 := dvd_sub h3i h4i
        have heqi : (f x : ℤ) * 5 - (g x : ℤ) * 12 = 11 := by
          rw [h₀, h₁]
          push_cast
          ring
        rw [heqi] at h5i
        exact_mod_cast h5i
      have hprime : Nat.Prime 11 := by norm_num
      rcases (Nat.dvd_prime hprime).mp hdvd with h | h
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        exact h
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        right
        exact h
    · intro hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl
      · refine ⟨1, ?_⟩
        rw [h₂, h₀, h₁]
        decide
      · refine ⟨4, ?_⟩
        rw [h₂, h₀, h₁]
        decide
  have hfin : (Set.range h).toFinset = {1, 11} := by
    ext k
    simp [hrange]
  rw [hfin, Finset.sum_insert (by norm_num), Finset.sum_singleton]
