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
    have hf0 : ∀ b, f (f b) = f 0 + 2 * f b := by
      intro b
      have h1 := h 0 b
      simp only [mul_zero, zero_add] at h1
      omega
    have hf2 : ∀ a, f (2 * a) = 2 * f a - f 0 := by
      intro a
      have h1 := hf0 a
      have h2 := h a 0
      simp only [add_zero] at h2
      omega
    have hadd : ∀ a b, f (a + b) = f a + f b - f 0 := by
      intro a b
      have h1 := hf2 a
      have h2 := hf0 (a + b)
      have h3 := h a b
      omega
    have hlin_nat : ∀ n : ℕ, f (n : ℤ) = (f 1 - f 0) * (n : ℤ) + f 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        push_cast
        rw [hadd (n : ℤ) 1, ih]
        ring
    have hlin_neg_nat : ∀ n : ℕ, f (-(n : ℤ)) = (f 1 - f 0) * (-(n : ℤ)) + f 0 := by
      intro n
      have h1 := hadd (n : ℤ) (-(n : ℤ))
      simp only [add_neg_cancel] at h1
      rw [hlin_nat n] at h1
      have h2 : f (-(n : ℤ)) = 2 * f 0 - ((f 1 - f 0) * (n : ℤ) + f 0) := by omega
      rw [h2]
      ring
    have hlin : ∀ z : ℤ, f z = (f 1 - f 0) * z + f 0 := by
      intro z
      by_cases hz : 0 ≤ z
      · have hz' : z = (z.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
        rw [hz', hlin_nat]
      · have hz2 : 0 ≤ -z := by omega
        have hz' : z = - ((-z).toNat : ℤ) := by
          have h1 := Int.toNat_of_nonneg hz2
          omega
        rw [hz', hlin_neg_nat]
    have e0 : (f 1 - f 0) * f 0 = 2 * f 0 := by
      have h1 := hf0 0
      have h2 := hlin (f 0)
      omega
    have e1 : (f 1 - f 0) * f 1 = 2 * f 1 := by
      have h1 := hf0 1
      have h2 := hlin (f 1)
      omega
    have hk_eq : (f 1 - f 0) * (f 1 - f 0) = 2 * (f 1 - f 0) := by
      linear_combination e1 - e0
    have hk0 : (f 1 - f 0) * ((f 1 - f 0) - 2) = 0 := by
      linear_combination hk_eq
    have hk_cases : (f 1 - f 0 = 0) ∨ (f 1 - f 0 = 2) := by
      have h1 := mul_eq_zero.mp hk0
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by linarith)
    intro z
    rcases hk_cases with hk | hk
    · have ht0 : f 0 = 0 := by
        have h1 := e0
        rw [hk] at h1
        omega
      left
      have h1 := hlin z
      rw [hk, ht0] at h1
      simpa using h1
    · right
      refine ⟨f 0, fun w => ?_⟩
      have h1 := hlin w
      rw [hk] at h1
      exact h1
  · intro hR
    by_cases hz : ∀ z, f z = 0
    · intro a b
      simp [hz]
    · push_neg at hz
      obtain ⟨z0, hz0⟩ := hz
      have h2 := hR z0
      rcases h2 with hleft | ⟨c, hc⟩
      · exact absurd hleft hz0
      · intro a b
        have e1 := hc (2 * a)
        have e2 := hc b
        have e3 := hc (a + b)
        rw [e1, e2, e3, hc (2 * (a + b) + c)]
        ring
