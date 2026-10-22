import Mathlib

open scoped Nat
open scoped Real

/--
We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? -/
theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) =
      3702 := by
  have h₁ : n = 1 / 3 := h₀
  have h₂ : Int.floor (10 * n) = 3 := by
    rw [h₁]
    norm_num
  have h₃ : Int.floor (100 * n) = 33 := by
    rw [h₁]
    norm_num
  have h₄ : Int.floor (1000 * n) = 333 := by
    rw [h₁]
    norm_num
  have h₅ : Int.floor (10000 * n) = 3333 := by
    rw [h₁]
    norm_num
  rw [h₂, h₃, h₄, h₅]
  norm_num
