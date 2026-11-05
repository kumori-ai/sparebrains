import Mathlib

open scoped Nat
open scoped Real

/-- The four-digit number $\underline{374n}$ is divisible by 18. Find the units digit $n$. -/
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
  rcases h₁ with ⟨c, hc⟩
  have hn0 : 0 ≤ n := Nat.zero_le n
  have hc_le : c ≤ 208 := by
    by_contra hnot
    have hc_gt : 209 ≤ c := by omega
    linarith [hc, hc_gt, h₀, hn0]
  have hc_ge : 207 ≤ c := by
    by_contra hnot
    have hc_lt : c ≤ 206 := by omega
    linarith [hc, hc_lt, hn0]
  have hc_eq : c = 208 := by omega
  have hn : 374 * 10 + n = 18 * 208 := by
    rw [← hc_eq]
    exact hc
  norm_num at hn
  omega
