import Mathlib

open scoped Nat
open scoped Real

/--
Given a nonnegative real number $x,$ let $\langle x\rangle$ denote the fractional part of $x;$ that is, $\langle x\rangle=x-\lfloor x\rfloor,$ where $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x.$  Suppose that $a$ is positive, $\langle a^{-1}\rangle=\langle a^2\rangle,$ and $2< a^2< 3.$  Find the value of $a^{12}-144a^{-1}.$ -/
theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by
  have hf2 : Int.floor (a ^ 2) = 2 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨le_of_lt h₂, by linarith⟩
  have ha1 : 1 < a := by nlinarith [h₂, h₀, sq_nonneg a]
  have hpos : 0 < 1 / a := by positivity
  have hlt1 : 1 / a < 1 := by
    rw [div_lt_one h₀]
    exact ha1
  have hf1 : Int.floor (1 / a) = 0 := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨le_of_lt hpos, by linarith⟩
  rw [hf1, hf2] at h₁
  have hinv : 1 / a = a ^ 2 - 2 := by
    push_cast at h₁
    linarith
  have h1a : 1 = a * (a ^ 2 - 2) := by
    have h : a * (1 / a) = a * (a ^ 2 - 2) := by rw [hinv]
    rwa [mul_one_div_cancel (ne_of_gt h₀)] at h
  have hcube : a ^ 3 = 2 * a + 1 := by
    calc a ^ 3 = a * (a ^ 2 - 2) + 2 * a := by ring
      _ = 1 + 2 * a := by rw [← h1a]
      _ = 2 * a + 1 := by ring
  have hquad : a ^ 2 = a + 1 := by
    have hfact : (a + 1) * (a ^ 2 - a - 1) = 0 := by
      have h : (a + 1) * (a ^ 2 - a - 1) = a ^ 3 - 2 * a - 1 := by ring
      rw [h, hcube]
      ring
    have ha1ne : a + 1 ≠ 0 := ne_of_gt (by linarith)
    have hzero : a ^ 2 - a - 1 = 0 := by
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h ha1ne
      · exact h
    linarith
  have e4 : a ^ 4 = 3 * a + 2 := by
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (a + 1) ^ 2 := by rw [hquad]
      _ = a ^ 2 + 2 * a + 1 := by ring
      _ = (a + 1) + 2 * a + 1 := by rw [hquad]
      _ = 3 * a + 2 := by ring
  have e6 : a ^ 6 = 8 * a + 5 := by
    calc a ^ 6 = a ^ 4 * a ^ 2 := by ring
      _ = (3 * a + 2) * (a + 1) := by rw [e4, hquad]
      _ = 3 * a ^ 2 + 5 * a + 2 := by ring
      _ = 3 * (a + 1) + 5 * a + 2 := by rw [hquad]
      _ = 8 * a + 5 := by ring
  have e12 : a ^ 12 = 144 * a + 89 := by
    calc a ^ 12 = (a ^ 6) ^ 2 := by ring
      _ = (8 * a + 5) ^ 2 := by rw [e6]
      _ = 64 * a ^ 2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [hquad]
      _ = 144 * a + 89 := by ring
  have hinv2 : 1 / a = a - 1 := by
    rw [hinv, hquad]
    ring
  rw [e12, hinv2]
  ring
