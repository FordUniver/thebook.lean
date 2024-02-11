import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Function
open scoped BigOperators

/-- Definition of the Fermat numbers -/
def fermat (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

/-- The recurence relation satisfied by Fermat numbers -/
lemma fermat_prod_form (n : ℕ) : (∏ k in range n, fermat k) = fermat n - 2 := by {
  apply eq_tsub_of_add_eq
  zify
  induction' n with n ih
  · trivial
  · rw [prod_range_succ, eq_sub_iff_add_eq.2 ih]
    have h : fermat n * fermat n + 2 = fermat n.succ + 2 * fermat n := by
      unfold fermat; simp only [_root_.pow_succ, two_mul]; ring
    linarith
}

lemma fermat_prod_form_add_two (n : ℕ) : ∏ k in range n, fermat k + 2 = fermat n := by {
  sorry
}

/-- The Fermat numbers are strictly increasing -/
lemma fermat_strictMono : StrictMono fermat := by {
  sorry
}

lemma fermat_ge_three (n : ℕ) : fermat n ≥ 3 := by sorry
lemma fermat_ne_one (n : ℕ) : fermat n ≠ 1 := by {
  have h := fermat_ge_three n
  sorry
}

/-- Fermat numbers are odd -/
lemma fermat_odd (n : ℕ) : Odd (fermat n) := by {
  sorry
}

/-- Fermat numbers are pairwise coprime -/
lemma fermat_coprime (m n : ℕ) (m_ne_n: m ≠ n) : Nat.Coprime (fermat m) (fermat n) := by {
  sorry
}

lemma l1
  (a b x y : ℕ)
  (a_b_coprime: Nat.Coprime a b)
  (x_ne_1: x ≠ 1) (y_ne_1: y ≠ 1)
  (x_dvd_a : x ∣ a) (y_dvd_b : y ∣ b) : x ≠ y := by {
    by_contra x_eq_y
    subst x_eq_y
    rw [Nat.Coprime] at *
    have x_dvd_gcd : x ∣ Nat.gcd a b := Nat.dvd_gcd x_dvd_a y_dvd_b
    have x_dvd_one : x ∣ 1 := by {
      rw [a_b_coprime] at x_dvd_gcd
      exact x_dvd_gcd
    }
    have x_eq_one : x = 1 :=  Nat.dvd_one.mp x_dvd_one
    contradiction
}

theorem goldbach_infinitude_of_primes : ∃ P : ℕ → ℕ, Injective P ∧ ∀ k, (P k).Prime := by {
  choose P P_prime P_dvd_fermat using fun n ↦ Nat.exists_prime_and_dvd (fermat_ne_one n)
  have P_inj : Injective P := by {
    intros m n Pm_eq_Pn
    by_contra m_ne_n
    have Pm_ne_Pn : P m ≠ P n := l1
      (fermat m) (fermat n) (P m) (P n)
      (fermat_coprime m n m_ne_n)
      (P_prime m).ne_one (P_prime n).ne_one
      (P_dvd_fermat m) (P_dvd_fermat n)
    contradiction
  }
  exact ⟨P, P_inj, P_prime⟩
}

theorem goldbach_infinitude_primes_standardised : { p : ℕ | Nat.Prime p}.Infinite := by {
  obtain ⟨P, P_inj, P_im_prime⟩ := goldbach_infinitude_of_primes
  exact Set.infinite_of_injective_forall_mem P_inj P_im_prime
}
