import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ is defined on the set of integers and satisfies \[ f(n)=\begin{cases} n-3 & \text{if } n\ge 1000 \\ f(f(n+5)) & \text{if } n< 1000\end{cases}  \] Find $f(84)$. -/
theorem aime_1984_p7 (f : ℤ → ℤ) (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) : f 84 = 997 := by
  have hf999 : f 999 = 998 := by
    rw [h₁ 999 (by norm_num)]
    norm_num [h₀ 1004 (by norm_num), h₀ 1001 (by norm_num)]
  have hf998 : f 998 = 997 := by
    rw [h₁ 998 (by norm_num)]
    norm_num [h₀ 1003 (by norm_num), h₀ 1000 (by norm_num)]
  have hf997 : f 997 = 998 := by
    rw [h₁ 997 (by norm_num)]
    norm_num [h₀ 1002 (by norm_num), hf999]
  have hf996 : f 996 = 997 := by
    rw [h₁ 996 (by norm_num)]
    norm_num [h₀ 1001 (by norm_num), hf998]
  have hf995 : f 995 = 998 := by
    rw [h₁ 995 (by norm_num)]
    norm_num [h₀ 1000 (by norm_num), hf997]
  have key : ∀ m : ℕ, ∀ j : ℕ, j ≤ m → j ≤ 915 →
      f (999 - (j : ℤ)) = if j % 2 = 1 then 997 else 998 := by
    intro m
    induction m with
    | zero =>
      intro j hj hj915
      interval_cases j
      norm_num [hf999, hf998, hf997, hf996, hf995]
    | succ m ih =>
      intro j hj hj915
      rcases eq_or_lt_of_le hj with rfl | hjlt
      · by_cases hj5 : 5 ≤ m + 1
        · have hlt : (999 - ((m + 1 : ℕ) : ℤ)) < 1000 := by
            have hnn : (0 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by positivity
            linarith
          have harg : (999 - ((m + 1 : ℕ) : ℤ)) + 5
              = 999 - (((m + 1) - 5 : ℕ) : ℤ) := by
            rw [Nat.cast_sub hj5]
            push_cast
            ring
          rw [h₁ _ hlt, harg, ih ((m + 1) - 5) (by omega) (by omega)]
          by_cases hpar : (m + 1) % 2 = 1
          · have hmod : ¬ ((m + 1 - 5) % 2 = 1) := by omega
            rw [if_neg hmod, if_pos hpar, hf998]
          · have hmod : ((m + 1 - 5) % 2 = 1) := by omega
            rw [if_pos hmod, if_neg hpar, hf997]
        · have hj4 : m + 1 ≤ 4 := by omega
          have hm : m ≤ 3 := by omega
          interval_cases m <;> norm_num [hf999, hf998, hf997, hf996, hf995]
      · exact ih j (by omega) hj915
  have hfinal := key 915 915 le_rfl le_rfl
  norm_num at hfinal
  exact hfinal
