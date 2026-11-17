import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ is defined on the set of integers and satisfies \[ f(n)=\begin{cases} n-3 & \text{if } n\ge 1000 \\ f(f(n+5)) & \text{if } n< 1000\end{cases}  \] Find $f(84)$. -/
theorem aime_1984_p7 (f : ℤ → ℤ) (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) : f 84 = 997 := by
  have h999 : f 999 = 998 := by
    have hlt : (999 : ℤ) < 1000 := by norm_num
    rw [h₁ 999 hlt]
    have h1004 : f (999 + 5) = 1001 := by
      have := h₀ (999 + 5) (by norm_num)
      norm_num at this ⊢
      exact this
    rw [h1004]
    have h1001 : f 1001 = 998 := by
      have := h₀ 1001 (by norm_num)
      norm_num at this ⊢
      exact this
    exact h1001
  have h998 : f 998 = 997 := by
    have hlt : (998 : ℤ) < 1000 := by norm_num
    rw [h₁ 998 hlt]
    have h1003 : f (998 + 5) = 1000 := by
      have := h₀ (998 + 5) (by norm_num)
      norm_num at this ⊢
      exact this
    rw [h1003]
    have h1000 : f 1000 = 997 := by
      have := h₀ 1000 (by norm_num)
      norm_num at this ⊢
      exact this
    exact h1000
  have h997 : f 997 = 998 := by
    have hlt : (997 : ℤ) < 1000 := by norm_num
    rw [h₁ 997 hlt]
    have h1002 : f (997 + 5) = 999 := by
      have := h₀ (997 + 5) (by norm_num)
      norm_num at this ⊢
      exact this
    rw [h1002]
    exact h999
  have hmain : ∀ j : ℕ, f (999 - 5 * (j : ℤ)) = if Even j then (998 : ℤ) else 997 := by
    intro j
    induction j with
    | zero =>
        simp [h999]
    | succ j ih =>
        have hlt : 999 - 5 * ((j + 1 : ℕ) : ℤ) < 1000 := by
          have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
          push_cast
          omega
        rw [h₁ (999 - 5 * ((j + 1 : ℕ) : ℤ)) hlt]
        have harg : 999 - 5 * ((j + 1 : ℕ) : ℤ) + 5 = 999 - 5 * (j : ℤ) := by
          push_cast
          ring
        rw [harg]
        rw [ih]
        by_cases hj : Even j
        · have hnot : ¬ Even (j + 1) := by
            rw [Nat.even_add_one]
            exact fun h => h hj
          simp [hj, hnot, h998]
        · have h : Even (j + 1) := by
            rw [Nat.even_add_one]
            exact hj
          simp [hj, h, h997]
  have h183 : f 84 = 997 := by
    have h := hmain 183
    have hnot : ¬ Even (183 : ℕ) := by norm_num
    rw [if_neg hnot] at h
    norm_num at h
    exact h
  exact h183
