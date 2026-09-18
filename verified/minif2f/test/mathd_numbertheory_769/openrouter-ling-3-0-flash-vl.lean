import Mathlib

open scoped Nat
open scoped Real

/-- What is the remainder when $129^{34}+96^{38}$ is divided by $11$? -/
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  calc
    (129 ^ 34 + 96 ^ 38) % 11 = (129 ^ 34 % 11 + 96 ^ 38 % 11) % 11 := by simp [Nat.add_mod]
    _ = (8 ^ 34 % 11 + 8 ^ 38 % 11) % 11 := by simp [Nat.mod_mod] -- hmm, 129 % 11 = 8
