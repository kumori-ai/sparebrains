import Mathlib

open scoped Nat
open scoped Real

/--
The function $f$ is defined on the set of integers and satisfies \[ f(n)=\begin{cases} n-3 & \text{if } n\ge 1000 \\ f(f(n+5)) & \text{if } n< 1000\end{cases}  \] Find $f(84)$. -/
theorem aime_1984_p7 (f : ℤ → ℤ) (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) : f 84 = 997 := by
  -- First, we prove a lemma that for all n < 1000, f n = 997 + n % 2.
  have h_lemma : ∀ n, n < 1000 → f n = 997 + n % 2 := by
    intro n hn
    set m := Int.toNat (1000 - n) with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def]
      omega
    let P : ℕ → Prop := λ m => ∀ n, Int.toNat (1000 - n) = m → n < 1000 → f n = 997 + n % 2
    have hP : ∀ m, (∀ k < m, P k) → P m := by
      intro m IH n hm hn
      by_cases h : n + 5 ≥ 1000
      · have h_n5 : f (n + 5) = (n + 5) - 3 := h₀ (n + 5) h
        rw [h₁ n hn, h_n5]
        by_cases h2 : n + 2 ≥ 1000
        · grind
        · have h_lt : n + 2 < 1000 := by linarith
          have h_lt' : 1000 - (n + 2) < 1000 - n := by omega
          have h_nonneg : 0 ≤ 1000 - (n + 2) := by omega
          have hm_n2 : Int.toNat (1000 - (n + 2)) < m := by
            omega
          have h_n2 := IH (Int.toNat (1000 - (n + 2))) hm_n2 (n+2) rfl h_lt
          grind
      · have h_n5_lt : n + 5 < 1000 := by linarith
        have h_lt' : 1000 - (n + 5) < 1000 - n := by omega
        have h_nonneg : 0 ≤ 1000 - (n + 5) := by omega
        have hm_n5 : Int.toNat (1000 - (n + 5)) < m := by
          omega
        have h_n5 := IH (Int.toNat (1000 - (n + 5))) hm_n5 (n+5) rfl h_n5_lt
        rw [h₁ n hn, h_n5]
        have hx_lt : 997 + (n+5) % 2 < 1000 := by
          have : (n+5) % 2 ≤ 1 := by omega
          omega
        have h_lt'' : 1000 - (997 + (n+5) % 2) < 1000 - n := by
          omega
        have h_nonneg' : 0 ≤ 1000 - (997 + (n+5) % 2) := by omega
        have hx_measure_lt : Int.toNat (1000 - (997 + (n+5) % 2)) < m := by
          omega
        have hx := IH (Int.toNat (1000 - (997 + (n+5) % 2))) hx_measure_lt (997 + (n+5) % 2) rfl hx_lt
        rw [hx]
        omega
    have hPm : P m := Nat.strong_induction_on m hP
    exact hPm n rfl hn
  have h84 := h_lemma 84 (by norm_num)
  simpa [show (84 : ℤ) % 2 = 0 by norm_num] using h84
