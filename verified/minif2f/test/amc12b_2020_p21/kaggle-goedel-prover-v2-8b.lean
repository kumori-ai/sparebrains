import Mathlib

open scoped Nat
open scoped Real

/--
How many positive integers $n$ satisfy$$\dfrac{n+1000}{70} = \lfloor \sqrt{n} \rfloor?$$(Recall that $\lfloor x\rfloor$ is the greatest integer not exceeding $x$.)

$\textbf{(A) } 2 \qquad\textbf{(B) } 4 \qquad\textbf{(C) } 6 \qquad\textbf{(D) } 30 \qquad\textbf{(E) } 32$ -/
theorem amc12b_2020_p21 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) : S.card = 6 := by
  have h₁ : S = {400, 470, 2290, 2360, 2430, 2500} := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · -- Prove the forward direction: if n is in S, then n is one of the specified values
      intro h
      have h₁ : 0 < n := h.1
      have h₂ : (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n) := h.2
      have h₃ : (n : ℝ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
        have h₄ : (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n) := h₂
        field_simp at h₄ ⊢
        <;> ring_nf at h₄ ⊢ <;> norm_cast at h₄ ⊢ <;>
          linarith
      have h₄ : (n : ℝ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
        exact h₃
      have h₅ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
        norm_cast at h₄ ⊢
        <;> linarith
      have h₆ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
        exact h₅
      have h₇ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
        exact h₆
      -- Prove that n must be one of the specified values
      have h₈ : n = 400 ∨ n = 470 ∨ n = 2290 ∨ n = 2360 ∨ n = 2430 ∨ n = 2500 := by
        have h₉ : Int.floor (Real.sqrt n) = (n + 1000 : ℤ) / 70 := by
          have h₉₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
            exact h₅
          have h₉₂ : Int.floor (Real.sqrt n) = (n + 1000 : ℤ) / 70 := by
            omega
          exact h₉₂
        have h₁₀ : (n : ℝ) ≥ 0 := by positivity
        have h₁₁ : Int.floor (Real.sqrt n) ≤ Real.sqrt n := by
          exact Int.floor_le (Real.sqrt n)
        have h₁₂ : Real.sqrt n < Int.floor (Real.sqrt n) + 1 := by
          exact Int.lt_floor_add_one (Real.sqrt n)
        have h₁₃ : (Int.floor (Real.sqrt n) : ℝ) ≤ Real.sqrt n := by
          exact_mod_cast h₁₁
        have h₁₄ : Real.sqrt n < (Int.floor (Real.sqrt n) : ℝ) + 1 := by
          exact_mod_cast h₁₂
        have h₁₅ : (n : ℝ) < (Int.floor (Real.sqrt n) + 1 : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg n, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
        have h₁₆ : (n : ℝ) ≥ (Int.floor (Real.sqrt n) : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg n, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
        have h₁₇ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
          norm_cast at h₁₆ ⊢
          <;> nlinarith
        have h₁₈ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
          norm_cast at h₁₅ ⊢
          <;> nlinarith
        have h₁₉ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
          exact h₅
        have h₂₀ : Int.floor (Real.sqrt n) = (n + 1000 : ℤ) / 70 := by
          omega
        -- Check possible values of m = floor(sqrt(n))
        have h₂₁ : Int.floor (Real.sqrt n) = 20 ∨ Int.floor (Real.sqrt n) = 21 ∨ Int.floor (Real.sqrt n) = 47 ∨ Int.floor (Real.sqrt n) = 48 ∨ Int.floor (Real.sqrt n) = 49 ∨ Int.floor (Real.sqrt n) = 50 := by
          -- Use the inequalities to bound m
          have h₂₂ : Int.floor (Real.sqrt n) ≤ 50 := by
            by_contra h₂₂
            have h₂₃ : Int.floor (Real.sqrt n) ≥ 51 := by
              linarith
            have h₂₄ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₂₅ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            have h₂₆ : (Int.floor (Real.sqrt n) : ℤ) ≥ 51 := by
              exact_mod_cast h₂₃
            have h₂₇ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₂₈ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            have h₂₉ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
              exact h₅
            have h₃₀ : (n : ℤ) = 70 * Int.floor (Real.sqrt n) - 1000 := by
              omega
            have h₃₁ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₃₂ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            nlinarith
          have h₂₃ : Int.floor (Real.sqrt n) ≥ 20 := by
            by_contra h₂₃
            have h₂₄ : Int.floor (Real.sqrt n) ≤ 19 := by
              linarith
            have h₂₅ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₂₆ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            have h₂₇ : (Int.floor (Real.sqrt n) : ℤ) ≤ 19 := by
              exact_mod_cast h₂₄
            have h₂₈ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₂₉ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            have h₃₀ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
              exact h₅
            have h₃₁ : (n : ℤ) = 70 * Int.floor (Real.sqrt n) - 1000 := by
              omega
            have h₃₂ : (n : ℤ) ≥ (Int.floor (Real.sqrt n) : ℤ) ^ 2 := by
              exact h₁₇
            have h₃₃ : (n : ℤ) < (Int.floor (Real.sqrt n) + 1 : ℤ) ^ 2 := by
              exact h₁₈
            nlinarith
          have h₂₄ : Int.floor (Real.sqrt n) = 20 ∨ Int.floor (Real.sqrt n) = 21 ∨ Int.floor (Real.sqrt n) = 47 ∨ Int.floor (Real.sqrt n) = 48 ∨ Int.floor (Real.sqrt n) = 49 ∨ Int.floor (Real.sqrt n) = 50 := by
            interval_cases Int.floor (Real.sqrt n) <;> norm_num at h₂₀ ⊢ <;>
              (try omega) <;> (try norm_num at h₁₇ h₁₈ ⊢ <;> omega) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (20 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 400 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                }) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (21 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 470 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                }) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (47 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 2290 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                }) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (48 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 2360 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                }) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (49 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 2430 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                }) <;>
              (try
                {
                  have h₃₄ : (n : ℤ) = 70 * (50 : ℤ) - 1000 := by omega
                  have h₃₅ : n = 2500 := by
                    norm_cast at h₃₄ ⊢ <;> omega
                  omega
                })
          exact h₂₄
        -- Now we know m is one of the specified values, we can find n
        rcases h₂₁ with (h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁ | h₂₁) <;>
          (try omega) <;>
          (try
            {
              have h₃₀ : n = 400 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 20 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 20 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 400 := by
                  omega
                have h₃₅ : n = 400 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            }) <;>
          (try
            {
              have h₃₀ : n = 470 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 21 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 21 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 470 := by
                  omega
                have h₃₅ : n = 470 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            }) <;>
          (try
            {
              have h₃₀ : n = 2290 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 47 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 47 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 2290 := by
                  omega
                have h₃₅ : n = 2290 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            }) <;>
          (try
            {
              have h₃₀ : n = 2360 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 48 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 48 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 2360 := by
                  omega
                have h₃₅ : n = 2360 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            }) <;>
          (try
            {
              have h₃₀ : n = 2430 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 49 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 49 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 2430 := by
                  omega
                have h₃₅ : n = 2430 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            }) <;>
          (try
            {
              have h₃₀ : n = 2500 := by
                have h₃₁ : (n : ℤ) + 1000 = 70 * Int.floor (Real.sqrt n) := by
                  exact h₅
                have h₃₂ : Int.floor (Real.sqrt n) = 50 := by
                  omega
                have h₃₃ : (n : ℤ) + 1000 = 70 * 50 := by
                  rw [h₃₂] at h₃₁
                  exact h₃₁
                have h₃₄ : (n : ℤ) = 2500 := by
                  omega
                have h₃₅ : n = 2500 := by
                  norm_cast at h₃₄ ⊢
                  <;> omega
                exact h₃₅
              simp [h₃₀]
            })
        <;>
        (try omega) <;>
        (try
          {
            simp_all [Finset.mem_insert, Finset.mem_singleton]
            <;> norm_num
            <;> aesop
          })
      rcases h₈ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num [Finset.mem_insert, Finset.mem_singleton]
    · -- Prove the reverse direction: if n is one of the specified values, then n is in S
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case n = 400
        constructor
        · norm_num
        · have h₂ : (↑(400 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 400) := by
            have h₃ : Int.floor (Real.sqrt 400) = 20 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 400, Real.sq_sqrt (show 0 ≤ (400 : ℝ) by norm_num)]
              })
          exact h₂
      · -- Case n = 470
        constructor
        · norm_num
        · have h₂ : (↑(470 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 470) := by
            have h₃ : Int.floor (Real.sqrt 470) = 21 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 470, Real.sq_sqrt (show 0 ≤ (470 : ℝ) by norm_num)]
              })
          exact h₂
      · -- Case n = 2290
        constructor
        · norm_num
        · have h₂ : (↑(2290 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2290) := by
            have h₃ : Int.floor (Real.sqrt 2290) = 47 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 2290, Real.sq_sqrt (show 0 ≤ (2290 : ℝ) by norm_num)]
              })
          exact h₂
      · -- Case n = 2360
        constructor
        · norm_num
        · have h₂ : (↑(2360 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2360) := by
            have h₃ : Int.floor (Real.sqrt 2360) = 48 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 2360, Real.sq_sqrt (show 0 ≤ (2360 : ℝ) by norm_num)]
              })
          exact h₂
      · -- Case n = 2430
        constructor
        · norm_num
        · have h₂ : (↑(2430 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2430) := by
            have h₃ : Int.floor (Real.sqrt 2430) = 49 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 2430, Real.sq_sqrt (show 0 ≤ (2430 : ℝ) by norm_num)]
              })
          exact h₂
      · -- Case n = 2500
        constructor
        · norm_num
        · have h₂ : (↑(2500 : ℕ) + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt 2500) := by
            have h₃ : Int.floor (Real.sqrt 2500) = 50 := by
              norm_num [Int.floor_eq_iff, Real.le_sqrt, Real.sqrt_lt, Nat.cast_nonneg]
              <;>
              (try norm_num) <;>
              (try
                {
                  nlinarith [Real.sqrt_nonneg 2500, Real.sq_sqrt (show 0 ≤ (2500 : ℝ) by norm_num)]
                })
            rw [h₃]
            <;> norm_num <;>
            (try
              {
                nlinarith [Real.sqrt_nonneg 2500, Real.sq_sqrt (show 0 ≤ (2500 : ℝ) by norm_num)]
              })
          exact h₂
  
  have h₂ : S.card = 6 := by
    rw [h₁]
    <;> norm_num
    <;> rfl
  
  exact h₂
