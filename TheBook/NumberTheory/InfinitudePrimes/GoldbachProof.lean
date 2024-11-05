import Mathlib.Data.Fintype.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Fin
import Aesop

open Finset Function BigOperators

namespace GoldbachInfinitudePrimes

/-- Definition of the Fermat numbers -/
def F (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

/-- Fermat numbers are odd -/
lemma F_odd (n : ℕ) : Odd (F n) := Even.add_one ((Nat.even_pow' (NeZero.ne (2 ^ n))).mpr (Nat.even_iff.mpr rfl))

/-- Fermat numbers are at least 2 -/
lemma F_ge_two (n : ℕ) : F n ≥ 2 := Nat.le.step (Nat.le_self_pow (NeZero.ne (2 ^ n)) 2)

/-- The recurrence relation satisfied by Fermat numbers -/
lemma F_prod_form (n : ℕ) : (∏ k in range n, F k) = F n - 2 := by
  induction' n with n ih
  · exact rfl
  · calc  ∏ k in range (Nat.succ n), F k
      _ = (∏ k in range n, F k) * F n           := Finset.prod_range_succ F n
      _ = (F n - 2) * F n                       := by rw [ih]
      _ = (2 ^ 2 ^ n - 1) * (2 ^ 2 ^ n + 1)     := by exact rfl
      _ = 2 ^ (2 ^ Nat.succ n) - 1              := by simp [Nat.mul_sub_right_distrib, Nat.mul_add]; rw [tsub_add_tsub_cancel (Nat.le_mul_self (2 ^ 2 ^ n)) (Nat.one_le_two_pow)]; rw [←Nat.pow_two, ←Nat.pow_mul', ←Nat.pow_succ']
      _ = F (Nat.succ n) - 2                    := by exact rfl

/-- Two numbers are coprime iff all their divisors are one -/
lemma coprime_iff_divisors_one (k n : ℕ) : Nat.Coprime k n ↔ ∀ m, m ∣ k ∧ m ∣ n → m = 1 :=
  ⟨fun k_n_coprime _ => (fun ⟨m_dvd_k, m_dvd_n⟩ => Nat.eq_one_of_dvd_coprimes k_n_coprime m_dvd_k m_dvd_n),
   fun h => h (Nat.gcd k n) ⟨Nat.gcd_dvd_left k n, Nat.gcd_dvd_right k n⟩⟩

/-- Fermat numbers are pairwise coprime -/
lemma F_coprime (k n : ℕ) (k_ne_n: k ≠ n) : Nat.Coprime (F k) (F n) := by
  rw [coprime_iff_divisors_one]
  intro m ⟨m_dvd_Fk, m_dvd_Fn⟩

  wlog k_lt_n : k < n
  · exact this n k k_ne_n.symm m m_dvd_Fn m_dvd_Fk (lt_of_le_of_ne (le_of_not_gt k_lt_n) k_ne_n.symm)
  · have m_dvd_two  : m ∣ 2 := by
      rw [←Nat.sub_sub_self (F_ge_two n), ←F_prod_form]
      exact Nat.dvd_sub' m_dvd_Fn (Nat.dvd_trans m_dvd_Fk (dvd_prod_of_mem F (mem_range.mpr k_lt_n)))

    have m_ne_zero  : m ≠ 0    := ne_zero_of_dvd_ne_zero (Nat.succ_ne_zero 1) m_dvd_two
    have m_le_two   : m ≤ 2    := Nat.le_of_dvd (Nat.two_pos) m_dvd_two

    have m_ne_two   : m ≠ 2    := fun m_eq_two => Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (m_eq_two ▸ m_dvd_Fn)) (F_odd n)
    exact Nat.eq_of_lt_succ_of_not_lt (lt_of_le_of_ne m_le_two m_ne_two) (Nat.not_lt.mpr (Nat.one_le_iff_ne_zero.mpr m_ne_zero))

/-- Proof of the infinitude of primes --/
theorem infinitude_of_primes : ∃ P : ℕ → ℕ, Injective P ∧ ∀ k, (P k).Prime := by
  choose P P_prime P_dvd_fermat using fun n => Nat.exists_prime_and_dvd (ne_of_gt (F_ge_two n))
  have P_inj : Injective P := by
    intros m n Pm_eq_Pn
    have Pm_dvd_gcd   : P m ∣ Nat.gcd (F m) (F n)  := Nat.dvd_gcd (P_dvd_fermat m) (Pm_eq_Pn ▸ P_dvd_fermat n)
    by_contra m_ne_n
    have Pm_dvd_one   : P m ∣ 1                    := F_coprime m n m_ne_n ▸ Pm_dvd_gcd
    exact Nat.Prime.ne_one (P_prime m) (Nat.dvd_one.mp Pm_dvd_one)
  exact ⟨P, P_inj, P_prime⟩

end GoldbachInfinitudePrimes
