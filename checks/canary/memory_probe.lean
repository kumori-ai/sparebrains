import Mathlib

/-- Allocates without end: the probe of the judge's memory cap. -/
def hoard : Nat → Array (Array Nat) → Nat
  | 0, acc => acc.size
  | n+1, acc => hoard n (acc.push (Array.replicate 100000 n))

#eval hoard 100000000 #[]

theorem memory_probe : True := trivial
