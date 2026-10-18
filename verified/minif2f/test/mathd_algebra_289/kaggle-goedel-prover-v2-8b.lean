import Mathlib

open scoped Nat
open scoped Real

/--
The two positive integer solutions of the equation $x^2 - mx + n = 0$ are $k$ and $t$, where $m$ and $n$ are both prime numbers and $k > t$. What is the value of $m^n + n^m + k^t + t^k$? -/
theorem mathd_algebra_289 (k t m n : ℕ) (h₀ : Nat.Prime m ∧ Nat.Prime n) (h₁ : t < k)
    (h₂ : (k ^ 2 : ℤ) - m * k + n = 0) (h₃ : (t ^ 2 : ℤ) - m * t + n = 0) :
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
  have h_k_pos : k ≥ 1 := by
    by_contra h
    -- Assume k = 0
    have h₄ : k = 0 := by
      omega
    -- Substitute k = 0 into h₂
    rw [h₄] at h₂
    norm_num at h₂
    -- Since n is a prime, n ≥ 2
    have h₅ : n = 0 := by
      omega
    have h₆ : Nat.Prime n := h₀.2
    have h₇ : n ≥ 2 := Nat.Prime.two_le h₆
    omega
  
  have h_t_pos : t ≥ 1 := by
    by_contra h
    have h₄ : t = 0 := by omega
    rw [h₄] at h₃
    norm_num at h₃
    have h₅ : n = 0 := by
      omega
    have h₆ : Nat.Prime n := h₀.2
    have h₇ : n ≥ 2 := Nat.Prime.two_le h₆
    omega
  
  have h_k_sq_add_n_eq_mk : k ^ 2 + n = m * k := by
    have h₄ : (k : ℤ) ^ 2 - m * k + n = 0 := h₂
    have h₅ : (k : ℤ) ^ 2 + n = m * k := by
      linarith
    have h₆ : k ^ 2 + n = m * k := by
      norm_cast at h₅ ⊢
      <;>
      (try omega) <;>
      (try ring_nf at h₅ ⊢ <;> omega)
    exact h₆
  
  have h_t_sq_add_n_eq_mt : t ^ 2 + n = m * t := by
    have h₄ : (t : ℤ) ^ 2 - m * t + n = 0 := h₃
    have h₅ : (t : ℤ) ^ 2 + n = m * t := by
      linarith
    have h₆ : t ^ 2 + n = m * t := by
      norm_cast at h₅ ⊢
      <;>
      (try omega) <;>
      (try ring_nf at h₅ ⊢ <;> omega)
    exact h₆
  
  have h_m_eq : m = k + t := by
    have h₄ : k ^ 2 + n = m * k := h_k_sq_add_n_eq_mk
    have h₅ : t ^ 2 + n = m * t := h_t_sq_add_n_eq_mt
    have h₆ : k ≥ t := by omega
    have h₇ : k ^ 2 - t ^ 2 = m * (k - t) := by
      have h₇₁ : k ^ 2 + n = m * k := h_k_sq_add_n_eq_mk
      have h₇₂ : t ^ 2 + n = m * t := h_t_sq_add_n_eq_mt
      have h₇₃ : k ^ 2 - t ^ 2 = m * (k - t) := by
        have h₇₄ : k ≥ t := by omega
        have h₇₅ : k ^ 2 ≥ t ^ 2 := by
          nlinarith
        have h₇₆ : m * k ≥ m * t := by
          nlinarith [h₀.1.two_le, h₀.2.two_le]
        have h₇₇ : k ^ 2 + n = m * k := h_k_sq_add_n_eq_mk
        have h₇₈ : t ^ 2 + n = m * t := h_t_sq_add_n_eq_mt
        have h₇₉ : k ^ 2 - t ^ 2 = m * (k - t) := by
          cases' le_iff_exists_add.mp h₇₄ with c hc
          simp [hc, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc] at h₇₇ h₇₈ ⊢
          <;> ring_nf at h₇₇ h₇₈ ⊢ <;> omega
        exact h₇₉
      exact h₇₃
    have h₈ : k ^ 2 - t ^ 2 = (k - t) * (k + t) := by
      have h₈₁ : k ≥ t := by omega
      have h₈₂ : k ^ 2 - t ^ 2 = (k - t) * (k + t) := by
        have h₈₃ : k ^ 2 ≥ t ^ 2 := by nlinarith
        have h₈₄ : k ^ 2 - t ^ 2 = (k - t) * (k + t) := by
          have h₈₅ : k ^ 2 - t ^ 2 = (k - t) * (k + t) := by
            cases' le_iff_exists_add.mp h₈₁ with c hc
            simp [hc, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
            <;> ring_nf <;> omega
          exact h₈₅
        exact h₈₄
      exact h₈₂
    have h₉ : m * (k - t) = (k - t) * (k + t) := by
      omega
    have h₁₀ : m = k + t := by
      have h₁₀₁ : k - t > 0 := by
        have h₁₀₂ : t < k := h₁
        omega
      have h₁₀₂ : m * (k - t) = (k - t) * (k + t) := h₉
      have h₁₀₃ : m = k + t := by
        apply Nat.eq_of_mul_eq_mul_right h₁₀₁
        nlinarith
      exact h₁₀₃
    exact h₁₀
  
  have h_n_eq : n = k * t := by
    have h₄ : k ^ 2 + n = m * k := h_k_sq_add_n_eq_mk
    have h₅ : m = k + t := h_m_eq
    rw [h₅] at h₄
    have h₆ : k ^ 2 + n = (k + t) * k := by linarith
    have h₇ : k ^ 2 + n = k ^ 2 + k * t := by
      ring_nf at h₆ ⊢
      <;> omega
    have h₈ : n = k * t := by
      omega
    exact h₈
  
  have h_t_eq_one : t = 1 := by
    have h₅ : Nat.Prime n := h₀.2
    have h₆ : n = k * t := h_n_eq
    have h₇ : k > t := by omega
    have h₈ : k ≥ 2 := by
      by_contra h
      have h₉ : k = 1 := by omega
      have h₁₀ : m = k + t := h_m_eq
      rw [h₉] at h₁₀
      have h₁₁ : m = 1 + t := by omega
      have h₁₂ : Nat.Prime m := h₀.1
      have h₁₃ : t ≥ 1 := h_t_pos
      have h₁₄ : m ≥ 2 := Nat.Prime.two_le h₁₂
      have h₁₅ : 1 + t ≥ 2 := by omega
      have h₁₆ : t < 1 := by
        nlinarith
      omega
    have h₉ : t = 1 := by
      by_contra h
      have h₁₀ : t ≥ 2 := by
        by_contra h₁₀
        have h₁₁ : t = 1 := by omega
        omega
      have h₁₁ : k * t ≥ k * 2 := by
        nlinarith
      have h₁₂ : k * t ≥ 2 * k := by
        nlinarith
      have h₁₃ : n = k * t := h_n_eq
      have h₁₄ : Nat.Prime n := h₀.2
      have h₁₅ : k * t ≥ 2 * k := by nlinarith
      have h₁₆ : k * t ≥ 2 * k := by nlinarith
      have h₁₇ : ¬Nat.Prime (k * t) := by
        have h₁₈ : k * t ≥ 2 * k := by nlinarith
        have h₁₉ : ¬Nat.Prime (k * t) := by
          by_cases h₂₀ : k = 1
          · exfalso
            omega
          · have h₂₁ : k ≥ 2 := by
              by_contra h₂₁
              omega
            have h₂₂ : t ≥ 2 := by omega
            have h₂₃ : k * t ≥ 2 * k := by nlinarith
            have h₂₄ : ¬Nat.Prime (k * t) := by
              have h₂₅ : k * t = k * t := rfl
              have h₂₆ : ¬Nat.Prime (k * t) := by
                apply Nat.not_prime_mul
                <;> omega
              exact h₂₆
            exact h₂₄
        exact h₁₉
      have h₁₈ : Nat.Prime n := h₀.2
      have h₁₉ : n = k * t := h_n_eq
      have h₂₀ : ¬Nat.Prime (k * t) := h₁₇
      have h₂₁ : ¬Nat.Prime n := by
        rw [h₁₉]
        exact h₂₀
      exact h₂₁ h₁₈
    exact h₉
  
  have h_k_eq_two : k = 2 := by
    have h₅ : m = k + t := h_m_eq
    have h₆ : n = k * t := h_n_eq
    have h₇ : t = 1 := h_t_eq_one
    have h₈ : k ≥ 2 := by
      by_contra h
      have h₉ : k = 1 := by omega
      have h₁₀ : m = k + t := h_m_eq
      rw [h₉] at h₁₀
      have h₁₁ : m = 1 + t := by omega
      have h₁₂ : Nat.Prime m := h₀.1
      have h₁₃ : t ≥ 1 := h_t_pos
      have h₁₄ : m ≥ 2 := Nat.Prime.two_le h₁₂
      have h₁₅ : 1 + t ≥ 2 := by omega
      have h₁₆ : t < 1 := by
        nlinarith
      omega
    have h₉ : k ≤ 2 := by
      by_contra h
      have h₁₀ : k ≥ 3 := by omega
      have h₁₁ : m = k + t := h_m_eq
      have h₁₂ : t = 1 := h_t_eq_one
      rw [h₁₂] at h₁₁
      have h₁₃ : m = k + 1 := by omega
      have h₁₄ : Nat.Prime m := h₀.1
      have h₁₅ : Nat.Prime k := by
        have h₁₅₁ : n = k * t := h_n_eq
        have h₁₅₂ : t = 1 := h_t_eq_one
        rw [h₁₅₂] at h₁₅₁
        have h₁₅₃ : n = k := by omega
        have h₁₅₄ : Nat.Prime n := h₀.2
        rw [h₁₅₃] at h₁₅₄
        exact h₁₅₄
      have h₁₆ : k ≥ 3 := h₁₀
      have h₁₇ : ¬Nat.Prime (k + 1) := by
        have h₁₇₁ : k % 2 = 1 := by
          have h₁₇₂ := Nat.Prime.eq_two_or_odd h₁₅
          omega
        have h₁₇₃ : (k + 1) % 2 = 0 := by
          omega
        have h₁₇₄ : 2 ∣ (k + 1) := by
          omega
        have h₁₇₅ : ¬Nat.Prime (k + 1) := by
          intro h₁₇₅
          have h₁₇₆ := Nat.Prime.eq_two_or_odd h₁₇₅
          omega
        exact h₁₇₅
      have h₁₈ : m = k + 1 := by omega
      have h₁₉ : ¬Nat.Prime m := by
        rw [h₁₈]
        exact h₁₇
      have h₂₀ : Nat.Prime m := h₀.1
      exact h₁₉ h₂₀
    have h₁₀ : k = 2 := by
      omega
    exact h₁₀
  
  have h_m_eq_three : m = 3 := by
    have h₅ : m = k + t := h_m_eq
    have h₆ : t = 1 := h_t_eq_one
    have h₇ : k = 2 := h_k_eq_two
    rw [h₆, h₇] at h₅
    <;> norm_num at h₅ ⊢
    <;> linarith
  
  have h_n_eq_two : n = 2 := by
    have h₅ : n = k * t := h_n_eq
    have h₆ : t = 1 := h_t_eq_one
    have h₇ : k = 2 := h_k_eq_two
    rw [h₆, h₇] at h₅
    <;> norm_num at h₅ ⊢
    <;> linarith
  
  have h_main : m ^ n + n ^ m + k ^ t + t ^ k = 20 := by
    have h₅ : m = 3 := h_m_eq_three
    have h₆ : n = 2 := h_n_eq_two
    have h₇ : k = 2 := h_k_eq_two
    have h₈ : t = 1 := h_t_eq_one
    simp [h₅, h₆, h₇, h₈, pow_succ, mul_assoc]
    <;> norm_num
    <;> ring_nf at *
    <;> norm_num
    <;> omega
  
  exact h_main
