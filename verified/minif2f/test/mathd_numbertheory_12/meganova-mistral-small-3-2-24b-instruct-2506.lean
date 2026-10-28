import Mathlib

open scoped Nat
open scoped Real

/-- How many integers between 15 and 85 are divisible by 20? -/
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  have : 20 ∣ 20 := by norm_num
  have : 20 ∣ 40 := by norm_num
  have : 20 ∣ 60 := by norm_num
  have : 20 ∣ 80 := by norm_num
  have : ¬20 ∣ 15 := by norm_num
  have : ¬20 ∣ 16 := by norm_num
  have : ¬20 ∣ 17 := by norm_num
  have : ¬20 ∣ 18 := by norm_num
  have : ¬20 ∣ 19 := by norm_num
  have : ¬20 ∣ 21 := by norm_num
  have : ¬20 ∣ 22 := by norm_num
  have : ¬20 ∣ 23 := by norm_num
  have : ¬20 ∣ 24 := by norm_num
  have : ¬20 ∣ 25 := by norm_num
  have : ¬20 ∣ 26 := by norm_num
  have : ¬20 ∣ 27 := by norm_num
  have : ¬20 ∣ 28 := by norm_num
  have : ¬20 ∣ 29 := by norm_num
  have : ¬20 ∣ 30 := by norm_num
  have : ¬20 ∣ 31 := by norm_num
  have : ¬20 ∣ 32 := by norm_num
  have : ¬20 ∣ 33 := by norm_num
  have : ¬20 ∣ 34 := by norm_num
  have : ¬20 ∣ 35 := by norm_num
  have : ¬20 ∣ 36 := by norm_num
  have : ¬20 ∣ 37 := by norm_num
  have : ¬20 ∣ 38 := by norm_num
  have : ¬20 ∣ 39 := by norm_num
  have : ¬20 ∣ 41 := by norm_num
  have : ¬20 ∣ 42 := by norm_num
  have : ¬20 ∣ 43 := by norm_num
  have : ¬20 ∣ 44 := by norm_num
  have : ¬20 ∣ 45 := by norm_num
  have : ¬20 ∣ 46 := by norm_num
  have : ¬20 ∣ 47 := by norm_num
  have : ¬20 ∣ 48 := by norm_num
  have : ¬20 ∣ 49 := by norm_num
  have : ¬20 ∣ 50 := by norm_num
  have : ¬20 ∣ 51 := by norm_num
  have : ¬20 ∣ 52 := by norm_num
  have : ¬20 ∣ 53 := by norm_num
  have : ¬20 ∣ 54 := by norm_num
  have : ¬20 ∣ 55 := by norm_num
  have : ¬20 ∣ 56 := by norm_num
  have : ¬20 ∣ 57 := by norm_num
  have : ¬20 ∣ 58 := by norm_num
  have : ¬20 ∣ 59 := by norm_num
  have : ¬20 ∣ 61 := by norm_num
  have : ¬20 ∣ 62 := by norm_num
  have : ¬20 ∣ 63 := by norm_num
  have : ¬20 ∣ 64 := by norm_num
  have : ¬20 ∣ 65 := by norm_num
  have : ¬20 ∣ 66 := by norm_num
  have : ¬20 ∣ 67 := by norm_num
  have : ¬20 ∣ 68 := by norm_num
  have : ¬20 ∣ 69 := by norm_num
  have : ¬20 ∣ 70 := by norm_num
  have : ¬20 ∣ 71 := by norm_num
  have : ¬20 ∣ 72 := by norm_num
  have : ¬20 ∣ 73 := by norm_num
  have : ¬20 ∣ 74 := by norm_num
  have : ¬20 ∣ 75 := by norm_num
  have : ¬20 ∣ 76 := by norm_num
  have : ¬20 ∣ 77 := by norm_num
  have : ¬20 ∣ 78 := by norm_num
  have : ¬20 ∣ 79 := by norm_num
  have : ¬20 ∣ 81 := by norm_num
  have : ¬20 ∣ 82 := by norm_num
  have : ¬20 ∣ 83 := by norm_num
  have : ¬20 ∣ 84 := by norm_num
  have : ¬20 ∣ 85 := by norm_num
  rfl
