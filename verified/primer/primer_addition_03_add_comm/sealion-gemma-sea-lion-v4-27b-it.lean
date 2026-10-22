import Mathlib

/-- Natural Number Game (Lean 4), Addition world, level 3: add_comm (level boss). Restated over Mathlib's ℕ. Source: https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L03add_comm.lean, Apache-2.0. -/
theorem primer_addition_03_add_comm (a b : ℕ) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_succ, Nat.succ_add, ih, Nat.add_succ]
