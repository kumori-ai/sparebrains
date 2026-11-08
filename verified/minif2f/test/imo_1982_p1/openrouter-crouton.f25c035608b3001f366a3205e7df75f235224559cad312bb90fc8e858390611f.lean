import Mathlib

open scoped Nat
open scoped Real

/--
The function $f(n)$ is defined on the positive integers and takes non-negative integer values. $f(2)=0,f(3)>0,f(9999)=3333$ and for all $m,n:$ \[ f(m+n)-f(m)-f(n)=0 \text{ or } 1. \] Determine $f(1982)$. -/
theorem imo_1982_p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, 0 < m ∧ 0 < n → (f (m + n) - f m - f n : ℤ) = 0 ∨ (f (m + n) - f m - f n : ℤ) = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := by
  have basic : ∀ m n : ℕ, 0 < m → 0 < n →
      f m + f n ≤ f (m + n) ∧ f (m + n) ≤ f m + f n + 1 := by
    intro m n hm hn
    have h := h₀ m n ⟨hm, hn⟩
    rcases h with h | h <;> constructor <;> omega
  have hf4 := basic 2 2 (by norm_num) (by norm_num)
  have hf6a := basic 3 3 (by norm_num) (by norm_num)
  have hf6b := basic 2 4 (by norm_num) (by norm_num)
  rw [show 2 + 2 = 4 by norm_num] at hf4
  rw [show 3 + 3 = 6 by norm_num] at hf6a
  rw [show 2 + 4 = 6 by norm_num] at hf6b
  have hf3 : f 3 = 1 := by omega
  have step3 : ∀ d a : ℕ, 1 ≤ a → f (3 * a) + d ≤ f (3 * (a + d)) := by
    intro d
    induction d with
    | zero =>
      intro a ha
      simp
    | succ d ih =>
      intro a ha
      have ih' := ih a ha
      have hstep := basic (3 * (a + d)) 3 (by omega) (by norm_num)
      have e : 3 * (a + (d + 1)) = 3 * (a + d) + 3 := by ring
      rw [e]
      omega
  have key : ∀ k : ℕ, k + 1 ≤ 3333 → f (3 * (k + 1)) = k + 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hf3]
    | succ k ih =>
      intro hk
      have hk1 : k + 1 ≤ 3333 := by omega
      have ih' := ih hk1
      have hstep := basic (3 * (k + 1)) 3 (by omega) (by norm_num)
      have hfuture := step3 (3333 - (k + 2)) (k + 2) (by omega)
      have e : (k + 2) + (3333 - (k + 2)) = 3333 := by omega
      rw [e] at hfuture
      have e2 : (3 : ℕ) * 3333 = 9999 := by norm_num
      rw [e2, h₃] at hfuture
      have e3 : 3 * (k + 1 + 1) = 3 * (k + 1) + 3 := by ring
      have e4 : 3 * (k + 2) = 3 * (k + 1) + 3 := by ring
      rw [e4] at hfuture
      rw [e3]
      omega
  have hf1980 := key 659 (by norm_num)
  have hf5946 := key 1981 (by norm_num)
  rw [show 3 * (659 + 1) = 1980 by norm_num] at hf1980
  rw [show 3 * (1981 + 1) = 5946 by norm_num] at hf5946
  have hb1 := basic 1980 2 (by norm_num) (by norm_num)
  have hb2 := basic 1982 1982 (by norm_num) (by norm_num)
  have hb3 := basic 3964 1982 (by norm_num) (by norm_num)
  rw [show 1980 + 2 = 1982 by norm_num] at hb1
  rw [show 1982 + 1982 = 3964 by norm_num] at hb2
  rw [show 3964 + 1982 = 5946 by norm_num] at hb3
  omega
