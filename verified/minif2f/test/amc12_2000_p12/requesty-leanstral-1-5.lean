import Mathlib

open scoped Nat
open scoped Real

/--
Let $ A$, $ M$, and $ C$ be nonnegative integers such that $ A +{} M +{} C ={} 12$. What is the maximum value of $ A \cdot M \cdot C +{} A\cdot M +{} M \cdot C +{} C\cdot A$?

$ \textbf{(A)}\ 62 \qquad \textbf{(B)}\ 72 \qquad \textbf{(C)}\ 92 \qquad \textbf{(D)}\ 102 \qquad \textbf{(E)}\ 112$ -/
theorem amc12_2000_p12 :
    IsGreatest
      {(a*m*c + a*m + m*c + a*c) | (a : ℕ) (m : ℕ) (c : ℕ) (h₀ : a + m + c = 12)}
      112 := by
  constructor
  · refine ⟨4, 4, 4, ?_, ?_⟩
    · norm_num
    · norm_num
  · intro x hx
    rcases hx with ⟨a, m, c, hsum, rfl⟩
    have ha : a ≤ 12 := by omega
    have hm : m ≤ 12 := by omega
    have hc : c ≤ 12 := by omega
    have h_bound : ∀ a ∈ Finset.range 13, ∀ m ∈ Finset.range 13, ∀ c ∈ Finset.range 13, a + m + c = 12 → a*m*c + a*m + m*c + a*c ≤ 112 := by
      decide
    exact h_bound a (Finset.mem_range.mpr (by omega)) m (Finset.mem_range.mpr (by omega)) c (Finset.mem_range.mpr (by omega)) hsum
