import Mathlib

/-- Counts for longer than any judge timeout, in constant memory beyond Mathlib's own: the probe of
tools/judge_timeout_canary.py. -/
def spin : Nat → Nat → Nat
  | 0, a => a
  | n+1, a => spin n (a+1)

#eval spin 200000000000 0

theorem timeout_probe : True := trivial
