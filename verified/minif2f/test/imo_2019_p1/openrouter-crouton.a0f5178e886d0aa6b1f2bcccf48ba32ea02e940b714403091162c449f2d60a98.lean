import Mathlib

open scoped Nat
open scoped Real

/--
Let $\mathbb{Z}$ be the set of integers. Determine all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ such that, for all integers $a$ and $b$, $$f(2a)+2f(b)=f(f(a+b)).$$
[i]Proposed by Liam Baker, South Africa[/i] -/
theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  constructor
  · intro h
    have h1 : ∀ a, f (f a) = f (2 * a) + 2 * f 0 := by
      intro a
      have h' := h a 0
      simpa using h'.symm
    have h2 : ∀ b, f (2 * b) = 2 * f b - f 0 := by
      intro b
      have hb := h1 b
      have h0 := h 0 b
      simp at h0
      linarith [hb, h0]
    have hadd : ∀ a b, f (a + b) = f a + f b - f 0 := by
      intro a b
      have key := h a b
      have hfa := h1 (a + b)
      have e2a := h2 a
      have e2ab := h2 (a + b)
      linarith [key, hfa, e2a, e2ab]
    set d := f 0 with hd
    set k := f 1 - f 0 with hk
    have hf1 : f 1 = k + d := by
      rw [hk]
      ring
    have hnat : ∀ n : ℕ, f (n : ℤ) = k * (n : ℤ) + d := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.cast_zero, mul_zero, zero_add]
        exact hd.symm
      | succ n ih =>
        have step := hadd (n : ℤ) 1
        push_cast
        rw [step, ih, hf1]
        ring
    have hform : ∀ z : ℤ, f z = k * z + d := by
      intro z
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
      · exact hnat n
      · have hsum := hadd (n : ℤ) (-(n : ℤ))
        rw [show (n : ℤ) + (-(n : ℤ)) = 0 by ring] at hsum
        have hn := hnat n
        have hneg : f (-(n : ℤ)) = 2 * d - f (n : ℤ) := by linarith [hsum]
        rw [hneg, hn]
        ring
    have hf2 : f 2 = 2 * k + d := by
      rw [hform 2]
      ring
    have hff1 : f (f 1) = k * (k + d) + d := by
      rw [hf1]
      exact hform (k + d)
    have hff2 : f (f 2) = k * (2 * k + d) + d := by
      rw [hf2]
      exact hform (2 * k + d)
    have e1 : 2 * k + 3 * d = k * (k + d) + d := by
      have h10 := h 1 0
      simp only [mul_one, add_zero, ← hd] at h10
      rw [hf2, hff1] at h10
      linarith [h10]
    have e2 : 4 * k + 3 * d = k * (2 * k + d) + d := by
      have h11 := h 1 1
      simp only [mul_one] at h11
      rw [show (1 : ℤ) + 1 = 2 by norm_num] at h11
      rw [hff2, hf2, hf1] at h11
      linarith [h11]
    have fact1 : (k - 2) * (k + d) = 0 := by linear_combination -e1
    have fact2 : (k - 2) * (2 * k + d) = 0 := by linear_combination -e2
    by_cases hk2 : k = 2
    · intro z
      right
      exact ⟨d, fun z => by rw [hform z, hk2]⟩
    · have hkd : k + d = 0 := by
        rcases mul_eq_zero.mp fact1 with h' | h'
        · exfalso
          exact hk2 (by linarith [h'])
        · exact h'
      have h2kd : 2 * k + d = 0 := by
        rcases mul_eq_zero.mp fact2 with h' | h'
        · exfalso
          exact hk2 (by linarith [h'])
        · exact h'
      have hk0 : k = 0 := by linarith [hkd, h2kd]
      have hd0 : d = 0 := by linarith [hkd, hk0]
      intro z
      left
      rw [hform z, hk0, hd0]
      ring
  · intro hr
    by_cases hex : ∃ c, ∀ z, f z = 2 * z + c
    · obtain ⟨c, hc⟩ := hex
      intro a b
      simp only [hc]
      ring
    · have hz : ∀ z, f z = 0 := by
        intro z
        rcases hr z with h' | h'
        · exact h'
        · exfalso
          exact hex h'
      intro a b
      rw [hz (2 * a), hz b, hz (f (a + b))]
      norm_num
