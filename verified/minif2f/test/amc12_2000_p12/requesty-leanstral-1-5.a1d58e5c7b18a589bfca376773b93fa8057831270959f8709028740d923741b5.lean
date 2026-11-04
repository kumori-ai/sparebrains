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
  have h_bound : ∀ a ∈ Finset.range 13, ∀ m ∈ Finset.range 13, ∀ c ∈ Finset.range 13,
      a + m + c = 12 → a*m*c + a*m + m*c + a*c ≤ 112 := by
    decide
  have h_mem : 112 ∈ {(a*m*c + a*m + m*c + a*c) | (a : ℕ) (m : ℕ) (c : ℕ) (h₀ : a + m + c = 12)} := by
    refine ⟨4, 4, 4, ?_, ?_⟩
    · norm_num
    · norm_num
  refine ⟨h_mem, ?_⟩
  intro x hx
  rcases hx with ⟨a, m, c, hsum, rfl⟩
  have ha : a < 13 := by omega
  have hm : m < 13 := by omega
  have hc : c < 13 := by omega
  exact h_bound a (Finset.mem_range.mpr ha) m (Finset.mem_range.mpr hm) c (Finset.mem_range.mpr hc) hsum
