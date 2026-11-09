import Mathlib

open scoped Nat
open scoped Real

/--
The function $f(n)$ is defined on the positive integers and takes non-negative integer values. $f(2)=0,f(3)>0,f(9999)=3333$ and for all $m,n:$ \[ f(m+n)-f(m)-f(n)=0 \text{ or } 1. \] Determine $f(1982)$. -/
theorem imo_1982_p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, 0 < m ∧ 0 < n → (f (m + n) - f m - f n : ℤ) = 0 ∨ (f (m + n) - f m - f n : ℤ) = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := by
  have hadd : ∀ m n, 0 < m → 0 < n →
      f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1 := by
    intro m n hm hn
    rcases h₀ m n ⟨hm, hn⟩ with h | h
    · left; omega
    · right; omega
  have hf3 : f 3 = 1 := by
    have h4' : f 4 = 0 ∨ f 4 = 1 := by
      have h := hadd 2 2 (by norm_num) (by norm_num)
      simpa [h₁] using h
    have h6a' : f 6 = f 3 + f 3 ∨ f 6 = f 3 + f 3 + 1 := by
      have h := hadd 3 3 (by norm_num) (by norm_num)
      simpa using h
    have h6b' : f 6 = f 4 ∨ f 6 = f 4 + 1 := by
      have h := hadd 2 4 (by norm_num) (by norm_num)
      simpa [h₁] using h
    rcases h4' with h | h <;> rcases h6a' with h' | h' <;>
      rcases h6b' with h'' | h'' <;> omega
  have hlow : ∀ k, k ≤ f (3 * k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      by_cases hk : k = 0
      · subst hk; simp [hf3]
      · have hk' : 0 < k := Nat.pos_of_ne_zero hk
        have hkpos : 0 < 3 * k := by omega
        have h := hadd (3 * k) 3 hkpos (by norm_num)
        have heq : 3 * (k + 1) = 3 * k + 3 := by ring
        rw [heq]
        rcases h with h | h <;> rw [hf3] at h <;> omega
  have heq3 : ∀ k, 1 ≤ k → k ≤ 3333 → f (3 * k) = k := by
    intro k hk1 hk2
    have hlowk := hlow k
    have hup : f (3 * k) ≤ k := by
      by_cases hk3333 : k = 3333
      · subst hk3333
        have h9999 : (3 * 3333 : ℕ) = 9999 := by norm_num
        have hf : f (3 * 3333) = 3333 := by rw [h9999, h₃]
        omega
      · have hklt : k < 3333 := by omega
        have hkpos : 0 < 3 * k := by omega
        have htpos : 0 < 3 * (3333 - k) := by omega
        have h := hadd (3 * k) (3 * (3333 - k)) hkpos htpos
        have hsum : 3 * k + 3 * (3333 - k) = 9999 := by omega
        rw [hsum, h₃] at h
        have hlowt := hlow (3333 - k)
        rcases h with h | h <;> omega
    exact le_antisymm hup hlowk
  have hf1980 : f 1980 = 660 := by
    have h := heq3 660 (by norm_num) (by norm_num)
    have h660 : (3 * 660 : ℕ) = 1980 := by norm_num
    rw [h660] at h
    exact h
  have hge : 660 ≤ f 1982 := by
    have h := hadd 1980 2 (by norm_num) (by norm_num)
    have hsum : (1980 + 2 : ℕ) = 1982 := by norm_num
    rw [hsum, hf1980, h₁] at h
    rcases h with h | h <;> omega
  have hle : f 1982 ≤ 660 := by
    have h5946 : f 5946 = 1982 := by
      have h := heq3 1982 (by norm_num) (by norm_num)
      have h1982 : (3 * 1982 : ℕ) = 5946 := by norm_num
      rw [h1982] at h
      exact h
    have h1 := hadd 1982 1982 (by norm_num) (by norm_num)
    have h2 := hadd (1982 + 1982) 1982 (by norm_num) (by norm_num)
    have e2 : ((1982 + 1982) + 1982 : ℕ) = 5946 := by norm_num
    rw [e2, h5946] at h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  omega
