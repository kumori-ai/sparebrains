import Mathlib

open scoped Nat
open scoped Real

/--
In the year $ 2001$, the United States will host the International Mathematical Olympiad. Let $ I$, $ M$, and $ O$ be distinct positive integers such that the product $ I\cdot M \cdot O ={} 2001$. What's the largest possible value of the sum $ I +{} M +{} O$?

$ \textbf{(A)}\  23 \qquad \textbf{(B)}\ 55 \qquad \textbf{(C)}\  99 \qquad \textbf{(D)}\  111 \qquad \textbf{(E)}\ 671$ -/
theorem amc12_2000_p1 :
    IsGreatest
      { i + m + o |
        (i : ℕ) (m : ℕ) (o : ℕ)
        (h₀ : i ≠ 0 ∧ m ≠ 0 ∧ o ≠ 0 ∧ i ≠ m ∧ i ≠ o ∧ m ≠ o)
        (h₁ : i*m*o = 2001)}
      671 := by
  have key : ∀ a b c : ℕ, a < b → b < c → a * b * c = 2001 → a + b + c ≤ 671 := by
    intro a b c hab hbc hprod
    have ha0 : a ≠ 0 := by rintro rfl; simp at hprod
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    have hdvd_a : a ∣ 2001 := ⟨b * c, by rw [← hprod]; ring⟩
    have h1 : a * (a + 1) * (a + 2) ≤ 2001 := by
      have hle : a * (a + 1) * (a + 2) ≤ a * b * c := by gcongr <;> omega
      omega
    have ha_le : a ≤ 12 := by
      by_contra h
      push_neg at h
      have hle : 13 * 14 * 15 ≤ a * (a + 1) * (a + 2) := by gcongr <;> omega
      omega
    have hb_le : b ≤ 44 := by
      have hbc_le : b * c ≤ 2001 := by
        have h1' : b * c ≤ a * (b * c) := Nat.le_mul_of_pos_left _ ha_pos
        have h2 : a * (b * c) = 2001 := by rw [← hprod]; ring
        omega
      have hbb : b * b ≤ 2001 := by
        have hle : b * b ≤ b * c := by gcongr <;> omega
        omega
      by_contra h
      push_neg at h
      have hle : 45 * 45 ≤ b * b := by gcongr <;> omega
      omega
    interval_cases a <;> first | omega | (interval_cases b <;> omega)
  constructor
  · exact ⟨1, 3, 667, by decide, by decide, rfl⟩
  · intro s hs
    obtain ⟨i, m, o, hdist, hprod, rfl⟩ := hs
    obtain ⟨hi0, hm0, ho0, him, hio, hmo⟩ := hdist
    have p1 : i * m * o = 2001 := hprod
    have p2 : i * o * m = 2001 := by rw [show i * o * m = i * m * o by ring]; exact hprod
    have p3 : m * i * o = 2001 := by rw [show m * i * o = i * m * o by ring]; exact hprod
    have p4 : m * o * i = 2001 := by rw [show m * o * i = i * m * o by ring]; exact hprod
    have p5 : o * i * m = 2001 := by rw [show o * i * m = i * m * o by ring]; exact hprod
    have p6 : o * m * i = 2001 := by rw [show o * m * i = i * m * o by ring]; exact hprod
    rcases lt_or_gt_of_ne him with him | him <;>
      rcases lt_or_gt_of_ne hio with hio | hio <;>
      rcases lt_or_gt_of_ne hmo with hmo | hmo <;>
      first
        | (exfalso; omega)
        | (have h := key i m o (by omega) (by omega) p1; omega)
        | (have h := key i o m (by omega) (by omega) p2; omega)
        | (have h := key m i o (by omega) (by omega) p3; omega)
        | (have h := key m o i (by omega) (by omega) p4; omega)
        | (have h := key o i m (by omega) (by omega) p5; omega)
        | (have h := key o m i (by omega) (by omega) p6; omega)
