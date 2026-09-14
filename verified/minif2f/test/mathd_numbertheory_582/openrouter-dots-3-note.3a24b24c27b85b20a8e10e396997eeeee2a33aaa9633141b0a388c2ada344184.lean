import Mathlib

open scoped Nat
open scoped Real

/--
If $n$ is a multiple of three, what is the remainder when $(n + 4) + (n + 6) + (n + 8)$ is divided by $9$? -/
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by
  have h2 : 9 ∣ n + 4 + (n + 6) + (n + 8) := by
    rcases h₁ with ⟨k, hk⟩
    subst hk
    -- goal: 9 ∣ 3*k + 4 + (3*k + 6) + (3*k + 8)
    -- simplify to 9*(k+2)
    -- we can use `omega` or `nlinarith` or `ring` with `simp`
    -- using `omega`:
    omega
  -- then use `Nat.mod_eq_zero_of_dvd`
  exact Nat.mod_eq_zero_of_dvd h2
