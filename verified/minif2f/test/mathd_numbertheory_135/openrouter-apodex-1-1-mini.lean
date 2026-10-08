import Mathlib

open scoped Nat
open scoped Real

/--
Let $n = 3^{17} + 3^{10}$. It is known that $11$ divides into $n+1$. If $n$ can be written in base $10$ as $ABCACCBAB$, where $A,B,C$ are distinct digits such that $A$ and $C$ are odd and $B$ is not divisible by $3$, find $100A + 10B + C$. -/
theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by
  have h₇ : n = 129199212 := by
    rw [h₀]
    norm_num
  rw [h₇] at h₆
  have h₈ : Nat.digits 10 129199212 = [2, 1, 2, 9, 9, 1, 9, 2, 1] := by
    decide
  rw [h₈] at h₆
  have h₉ : B = 2 := by
    have h₉ := h₆
    aesop
  have h₁₀ : A = 1 := by
    have h₁₀ := h₆
    aesop
  have h₁₁ : C = 9 := by
    have h₁₁ := h₆
    aesop
  rw [h₉, h₁₀, h₁₁]