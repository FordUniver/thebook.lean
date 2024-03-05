import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Finite

open BigOperators

namespace EuclidInfinitudePrimes

theorem infinitude_primes
  (S : Finset ℕ) (hS : ∀ s ∈ S, Nat.Prime s) : ∃ p, Nat.Prime p ∧ p ∉ S := by
    let n := (∏ i in S, i) + 1

    have n_ne_one : n ≠ 1 := by
      rw [Nat.succ_ne_succ, Finset.prod_ne_zero_iff]
      exact fun s s_in_S ↦ Nat.Prime.ne_zero (hS s s_in_S)

    obtain ⟨p, p_prime, p_dvd_n⟩ := Nat.exists_prime_and_dvd n_ne_one

    have p_not_in_S : p ∉ S := by
      by_contra p_in_S
      have p_dvd_ProdS   :   p ∣ (∏ i in S, i)  := Finset.dvd_prod_of_mem (fun i ↦ i) p_in_S
      have p_dvd_one     :   p ∣ 1              := (Nat.dvd_add_right p_dvd_ProdS).mp p_dvd_n
      have p_not_dvd_one :  ¬p ∣ 1              := Nat.Prime.not_dvd_one p_prime
      contradiction

    exact ⟨p, p_prime, p_not_in_S⟩

end EuclidInfinitudePrimes
