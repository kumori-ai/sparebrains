import Mathlib

open scoped Nat
open scoped Real

/--
Let $f(x) = 12x+7$ and $g(x) = 5x+2$ whenever $x$ is a positive integer. Define $h(x)$ to be the greatest common divisor of $f(x)$ and $g(x)$. What is the sum of all possible values of $h(x)$? -/
theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
    (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
    ∑ k ∈ (Set.range h).toFinset, k = 12 := by
  have h₄ : ∀ (x : ℕ+), h x = 1 ∨ h x = 11 := by
    intro x
    rw [h₂, h₀, h₁]
    have h₅ : x.val ≥ 1 := x.prop
    have h₆ : x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val ≥ 5 := by
      omega
    rcases h₆ with (h₆ | h₆ | h₆ | h₆ | h₆)
    · aesop
    · aesop
    · aesop
    · aesop
    · -- Case x.val ≥ 5
      have h₇ : x.val ≥ 5 := h₆
      have h₈ : Nat.gcd (12 * x.val + 7) (5 * x.val + 2) = Nat.gcd 11 (x.val - 4) := by
        have h₉ : 12 * x.val + 7 = 2 * (5 * x.val + 2) + (2 * x.val + 3) := by
          ring_nf
          <;> omega
        have h₁₀ : 5 * x.val + 2 = 2 * (2 * x.val + 3) + (x.val - 4) := by
          have h₁₁ : x.val ≥ 5 := h₇
          have h₁₂ : x.val ≥ 4 := by omega
          have h₁₃ : 5 * x.val + 2 = 2 * (2 * x.val + 3) + (x.val - 4) := by
            omega
          exact h₁₃
        have h₁₄ : 2 * x.val + 3 = 2 * (x.val - 4) + 11 := by
          have h₁₅ : x.val ≥ 5 := h₇
          have h₁₆ : x.val ≥ 4 := by omega
          have h₁₇ : 2 * x.val + 3 = 2 * (x.val - 4) + 11 := by
            omega
          exact h₁₇
        have h₁₈ : Nat.gcd (12 * x.val + 7) (5 * x.val + 2) = Nat.gcd (5 * x.val + 2) (2 * x.val + 3) := by
          rw [h₉]
          <;> simp [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_add_mul_right_right]
          <;> ring_nf at *
          <;> omega
        have h₁₉ : Nat.gcd (5 * x.val + 2) (2 * x.val + 3) = Nat.gcd (2 * x.val + 3) (x.val - 4) := by
          rw [h₁₀]
          <;> simp [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_add_mul_right_right]
          <;> ring_nf at *
          <;> omega
        have h₂₀ : Nat.gcd (2 * x.val + 3) (x.val - 4) = Nat.gcd 11 (x.val - 4) := by
          rw [h₁₄]
          <;> simp [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_add_mul_right_right]
          <;> ring_nf at *
          <;> omega
        rw [h₁₈, h₁₉, h₂₀]
      have h₂₁ : Nat.gcd 11 (x.val - 4) = 1 ∨ Nat.gcd 11 (x.val - 4) = 11 := by
        have hprime : Nat.Prime 11 := by norm_num
        have hgcd_dvd : Nat.gcd (11 : ℕ) (↑x - (4 : ℕ)) ∣ (11 : ℕ) := Nat.gcd_dvd_left _ _
        exact hprime.eq_one_or_self_of_dvd _ hgcd_dvd
      rcases h₂₁ with (h₂₁ | h₂₁) <;> simp [h₈, h₂₁]
      <;> norm_num at *
      <;> omega
  
  have h₅ : (Set.range h).toFinset = {1, 11} := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_toFinset, Set.mem_range]
    constructor
    · -- Prove the forward direction: if k is in the toFinset of Set.range h, then k is either 1 or 11.
      intro h₅
      rcases h₅ with ⟨x, rfl⟩
      have h₆ : h x = 1 ∨ h x = 11 := h₄ x
      rcases h₆ with (h₆ | h₆) <;> simp [h₆]
    · -- Prove the reverse direction: if k is either 1 or 11, then k is in the toFinset of Set.range h.
      intro h₅
      rcases h₅ with (rfl | rfl)
      · -- Case k = 1
        -- We need to find an x such that h x = 1.
        have h₆ : ∃ (x : ℕ+), h x = 1 := by
          -- We can choose x = 1, x = 2, or x = 3 to get h x = 1.
          use 1
          have h₇ : h (1 : ℕ+) = 1 := by
            rw [h₂, h₀, h₁]
            <;> norm_num [Nat.gcd_eq_right]
          exact h₇
        rcases h₆ with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
      · -- Case k = 11
        -- We need to find an x such that h x = 11.
        have h₆ : ∃ (x : ℕ+), h x = 11 := by
          -- We can choose x = 4 to get h x = 11.
          use 4
          have h₇ : h (4 : ℕ+) = 11 := by
            rw [h₂, h₀, h₁]
            <;> norm_num [Nat.gcd_eq_right]
          exact h₇
        rcases h₆ with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
  
  have h₆ : ∑ k ∈ (Set.range h).toFinset, k = 12 := by
    rw [h₅]
    norm_num
    <;>
    simp [Finset.sum_pair (show (1 : ℕ) ≠ 11 by norm_num)]
    <;>
    norm_num
    <;>
    rfl
  
  apply h₆
