import Mathlib

open scoped Nat
open scoped Real

/-- What is the product of all odd positive integers less than 10000?

$ \textbf{(A)} \ \frac {10000!}{(5000!)^2} \qquad \textbf{(B)} \ \frac {10000!}{2^{5000}} \ \qquad \textbf{(C)} \ \frac {9999!}{2^{5000}} \qquad \textbf{(D)} \ \frac {10000!}{2^{5000} \cdot 5000!} \qquad \textbf{(E)} \ \frac {5000!}{2^{5000}}$ -/
theorem amc12_2001_p5 :
    Finset.prod (Finset.filter (fun x => ¬Even x) (Finset.range 10000)) (id : ℕ → ℕ) =
      10000! / (2 ^ 5000 * 5000!) := by
  have key : ∀ n : ℕ, (2 ^ n * Nat.factorial n) *
      (∏ x ∈ Finset.range (2 * n), if ¬Even x then x else 1) = Nat.factorial (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hprod : (∏ x ∈ Finset.range (2 * (n + 1)), if ¬Even x then x else 1)
          = (∏ x ∈ Finset.range (2 * n), if ¬Even x then x else 1) * (2 * n + 1) := by
        have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
        rw [h1, Finset.prod_range_succ, Finset.prod_range_succ]
        have heven : Even (2 * n) := ⟨n, by ring⟩
        have hneven : ¬Even (2 * n + 1) := by
          rintro ⟨k, hk⟩
          omega
        rw [if_neg (fun h => h heven), if_pos hneven]
        simp
      calc (2 ^ (n + 1) * Nat.factorial (n + 1)) *
            (∏ x ∈ Finset.range (2 * (n + 1)), if ¬Even x then x else 1)
          = ((2 ^ n * Nat.factorial n) *
              (∏ x ∈ Finset.range (2 * n), if ¬Even x then x else 1)) *
              (2 * (n + 1) * (2 * n + 1)) := by
            rw [hprod, pow_succ, Nat.factorial_succ]; ring
        _ = Nat.factorial (2 * n) * (2 * (n + 1) * (2 * n + 1)) := by rw [ih]
        _ = Nat.factorial (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ,
              Nat.factorial_succ]; ring
  have hfilter : Finset.prod (Finset.filter (fun x => ¬Even x) (Finset.range 10000))
        (id : ℕ → ℕ)
      = ∏ x ∈ Finset.range 10000, if ¬Even x then x else 1 := by
    simp only [Finset.prod_filter, id_eq]
  rw [hfilter]
  have h10000 : (2 : ℕ) * 5000 = 10000 := by norm_num
  have key5000 := key 5000
  rw [h10000] at key5000
  have hpos : 0 < 2 ^ 5000 * Nat.factorial 5000 :=
    Nat.mul_pos (by positivity) (Nat.factorial_pos 5000)
  rw [← key5000, Nat.mul_div_cancel_left _ hpos]
