import Mathlib

/-- Natural Number Game (Lean 4), Implication world, level 4: succ_inj. Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Implication/L04succ_inj.lean, Apache-2.0. -/
theorem primer_implication_04_succ_inj (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  omega
