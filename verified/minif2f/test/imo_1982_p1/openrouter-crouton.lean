import Mathlib

open scoped Nat
open scoped Real

/--
The function $f(n)$ is defined on the positive integers and takes non-negative integer values. $f(2)=0,f(3)>0,f(9999)=3333$ and for all $m,n:$ \[ f(m+n)-f(m)-f(n)=0 \text{ or } 1. \] Determine $f(1982)$. -/
theorem imo_1982_p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, 0 < m ∧ 0 < n → (f (m + n) - f m - f n : ℤ) = 0 ∨ (f (m + n) - f m - f n : ℤ) = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := by
  have hstep : ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1 := by
    intro m n hm hn
    rcases h₀ m n ⟨hm, hn⟩ with h | h
    · left; omega
    · right; omega
  have hmult : ∀ (m k : ℕ), 0 < m →
      (k + 1) * f m ≤ f ((k + 1) * m) ∧ f ((k + 1) * m) ≤ (k + 1) * f m + k := by
    intro m k hm
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : 0 < (k + 1) * m := Nat.mul_pos (Nat.succ_pos k) hm
      have hstep' := hstep ((k + 1) * m) m hpos hm
      have e1 : (k + 1 + 1) * m = (k + 1) * m + m := by ring
      have e2 : (k + 1 + 1) * f m = (k + 1) * f m + f m := by ring
      rw [e1, e2]
      rcases hstep' with h | h <;> omega
  have hA := hmult 1982 9998 (by norm_num)
  have hB := hmult 9999 1981 (by norm_num)
  norm_num at hA hB
  rw [h₃] at hB
  omega
