import Mathlib

open scoped Nat
open scoped Real

/-- Prove that for any n natural, the number \[ \sum \limits_{k=0}^{n} \binom{2n+1}{2k+1} 2^{3k}  \]
cannot be divided by $5$. -/
theorem imo_1974_p3 (n : ℕ) :
    ¬5 ∣ ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 2 ^ (3 * k) := by
  set A' := ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 8 ^ k with hA'def
  set B := ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k) * 8 ^ k with hBdef
  have hSA : (∑ k ∈ Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 2 ^ (3 * k)) = A' := by
    rw [hA'def]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [pow_mul]
    norm_num
  have hsplit : ∀ f : ℕ → ℝ,
      ∑ j ∈ Finset.range (2 * n + 2), f j =
        ∑ k ∈ Finset.range (n + 1), f (2 * k) + ∑ k ∈ Finset.range (n + 1), f (2 * k + 1) := by
    intro f
    have hEven : Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * n + 2)) =
        (Finset.range (n + 1)).image (fun k => 2 * k) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hmod⟩
        exact ⟨j / 2, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨by omega, by omega⟩
    have hOdd : Finset.filter (fun j => j % 2 = 1) (Finset.range (2 * n + 2)) =
        (Finset.range (n + 1)).image (fun k => 2 * k + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hmod⟩
        exact ⟨j / 2, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨by omega, by omega⟩
    have hNot : Finset.filter (fun j => ¬ j % 2 = 0) (Finset.range (2 * n + 2)) =
        Finset.filter (fun j => j % 2 = 1) (Finset.range (2 * n + 2)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hj, hmod⟩
        exact ⟨hj, by omega⟩
      · rintro ⟨hj, hmod⟩
        exact ⟨hj, by omega⟩
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (2 * n + 2))
      (fun j => j % 2 = 0) f
    rw [hNot] at hsum
    have hsumEven : ∑ j ∈ Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * n + 2)), f j =
        ∑ k ∈ Finset.range (n + 1), f (2 * k) := by
      rw [hEven]
      apply Finset.sum_image
      intro x _ y _ hxy
      have h : 2 * x = 2 * y := hxy
      omega
    have hsumOdd : ∑ j ∈ Finset.filter (fun j => j % 2 = 1) (Finset.range (2 * n + 2)), f j =
        ∑ k ∈ Finset.range (n + 1), f (2 * k + 1) := by
      rw [hOdd]
      apply Finset.sum_image
      intro x _ y _ hxy
      have h : 2 * x + 1 = 2 * y + 1 := hxy
      omega
    rw [← hsum, hsumEven, hsumOdd]
  have key : ∀ t : ℝ, t ^ 2 = 8 → (1 + t) ^ (2 * n + 1) = (B : ℝ) + (A' : ℝ) * t := by
    intro t ht
    have hexp : (1 + t) ^ (2 * n + 1) =
        ∑ j ∈ Finset.range (2 * n + 2), t ^ j * (Nat.choose (2 * n + 1) j : ℝ) := by
      calc (1 + t) ^ (2 * n + 1) = (t + 1) ^ (2 * n + 1) := by rw [add_comm]
        _ = ∑ k ∈ Finset.range (2 * n + 2),
              t ^ k * (1 : ℝ) ^ (2 * n + 1 - k) * (Nat.choose (2 * n + 1) k : ℝ) :=
            add_pow t 1 (2 * n + 1)
        _ = ∑ k ∈ Finset.range (2 * n + 2), t ^ k * (Nat.choose (2 * n + 1) k : ℝ) := by simp
    have hEvenSum : ∑ k ∈ Finset.range (n + 1),
        t ^ (2 * k) * (Nat.choose (2 * n + 1) (2 * k) : ℝ) = (B : ℝ) := by
      rw [hBdef]
      push_cast
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_mul, ht, mul_comm]
    have hOddSum : ∑ k ∈ Finset.range (n + 1),
        t ^ (2 * k + 1) * (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) = (A' : ℝ) * t := by
      rw [hA'def]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ, pow_mul, ht]
      ring
    rw [hexp, hsplit, hEvenSum, hOddSum]
  have hsqrt : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have eq1 := key (Real.sqrt 8) hsqrt
  have eq2 := key (-Real.sqrt 8) (by
    have h : (-Real.sqrt 8) ^ 2 = (Real.sqrt 8) ^ 2 := by ring
    rw [h, hsqrt])
  have eq2' : (1 - Real.sqrt 8) ^ (2 * n + 1) = (B : ℝ) - (A' : ℝ) * Real.sqrt 8 := by
    have h : (1 - Real.sqrt 8 : ℝ) = 1 + -Real.sqrt 8 := by ring
    rw [h, eq2]
    ring
  have hprod : (B : ℝ) ^ 2 - 8 * (A' : ℝ) ^ 2 = (-7 : ℝ) ^ (2 * n + 1) := by
    have h1 : ((B : ℝ) + (A' : ℝ) * Real.sqrt 8) * ((B : ℝ) - (A' : ℝ) * Real.sqrt 8) =
        (-7 : ℝ) ^ (2 * n + 1) := by
      rw [← eq1, ← eq2', ← mul_pow]
      have h : (1 + Real.sqrt 8) * (1 - Real.sqrt 8) = -7 := by
        calc (1 + Real.sqrt 8) * (1 - Real.sqrt 8) = 1 - (Real.sqrt 8) ^ 2 := by ring
          _ = -7 := by rw [hsqrt]; norm_num
      rw [h]
    have hexpand : ((B : ℝ) + (A' : ℝ) * Real.sqrt 8) * ((B : ℝ) - (A' : ℝ) * Real.sqrt 8) =
        (B : ℝ) ^ 2 - 8 * (A' : ℝ) ^ 2 := by
      calc ((B : ℝ) + (A' : ℝ) * Real.sqrt 8) * ((B : ℝ) - (A' : ℝ) * Real.sqrt 8)
          = (B : ℝ) ^ 2 - (A' : ℝ) ^ 2 * (Real.sqrt 8) ^ 2 := by ring
        _ = (B : ℝ) ^ 2 - 8 * (A' : ℝ) ^ 2 := by rw [hsqrt]; ring
    rw [hexpand] at h1
    exact h1
  have hint : (B : ℤ) ^ 2 - 8 * (A' : ℤ) ^ 2 = (-7 : ℤ) ^ (2 * n + 1) := by
    have h2 : (((B : ℤ) ^ 2 - 8 * (A' : ℤ) ^ 2 : ℤ) : ℝ) = (((-7 : ℤ) ^ (2 * n + 1) : ℤ) : ℝ) := by
      push_cast
      push_cast at hprod
      exact hprod
    exact_mod_cast h2
  intro hdiv
  have hA0 : (A' : ZMod 5) = 0 := by
    have h : 5 ∣ A' := by rw [← hSA]; exact hdiv
    exact (CharP.cast_eq_zero_iff (ZMod 5) 5 A').mpr h
  have h5 : (B : ZMod 5) ^ 2 = (-7 : ZMod 5) ^ (2 * n + 1) := by
    have h := congrArg (fun x : ℤ => (x : ZMod 5)) hint
    push_cast at h
    rw [hA0] at h
    simpa using h
  have hRHS : (-7 : ZMod 5) ^ (2 * n + 1) = 3 * (-1) ^ n := by
    have h7 : (-7 : ZMod 5) = 3 := by decide
    have h32 : (3 : ZMod 5) ^ 2 = -1 := by decide
    calc (-7 : ZMod 5) ^ (2 * n + 1) = (3 : ZMod 5) ^ (2 * n + 1) := by rw [h7]
      _ = 3 * ((3 : ZMod 5) ^ 2) ^ n := by
          rw [pow_add, pow_mul]
          ring
      _ = 3 * (-1) ^ n := by rw [h32]
  rw [hRHS] at h5
  have hsq : ∀ x : ZMod 5, x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by decide
  have hcases : (-1 : ZMod 5) ^ n = 1 ∨ (-1 : ZMod 5) ^ n = -1 := neg_one_pow_eq_or (ZMod 5) n
  rcases hsq (B : ZMod 5) with h | h | h <;> rw [h] at h5 <;> rcases hcases with hc | hc <;> rw [hc] at h5 <;> revert h5 <;> decide
