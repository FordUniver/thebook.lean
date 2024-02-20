import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Function
open BigOperators


namespace GoldbachIfinitudePrimes


/-- Definition of the Fermat numbers -/
-- (1) Let us first look at the Fermat numbers Fn = 2 ^ 2 ^ n + 1 for n = 0, 1, 2, ... .
def F (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

/-- Fermat numbers are odd -/
-- (11) ... since all Fermat numbers are odd.
lemma F_odd (n : ℕ) : Odd (F n) := Even.add_one ((Nat.even_pow' (NeZero.ne (2 ^ n))).mpr (Nat.even_iff.mpr rfl))

/-- Fermat numbers are at least 2 -/
lemma F_ge_two (n : ℕ) : F n ≥ 2 := Nat.le.step (Nat.le_self_pow (NeZero.ne (2 ^ n)) 2)

/-- The recurrence relation satisfied by Fermat numbers -/
-- (4) To this end, we verify the recursion ...
lemma F_prod_form (n : ℕ) : (∏ k in range n, F k) = F n - 2 := by
  -- (12) To prove the recursion we use induction on n.
  induction' n with n ih
  -- (13) For n = 1 we have F0 = 3 and F1 − 2 = 3.
  · exact rfl
  -- (14) With induction we now conclude ...
  · calc  ∏ k in range (Nat.succ n), F k
      _ = (∏ k in range n, F k) * F n                                    := by rw [Finset.prod_range_succ] -- keep
      _ = (F n - 2) * F n                                                := by rw [ih] -- keep
      _ = (2 ^ 2 ^ n - 1) * (2 ^ 2 ^ n + 1)                              := by exact rfl -- keep
      _ = 2 ^ 2 ^ n * 2 ^ 2 ^ n + 2 ^ 2 ^ n * 1 - 1 * (2 ^ 2 ^ n + 1)    := by rw [Nat.mul_sub_right_distrib, Nat.mul_add]
      _ = 2 ^ 2 ^ n * 2 ^ 2 ^ n + 2 ^ 2 ^ n * 1 - (2 ^ 2 ^ n + 1)        := by ring
      _ = 2 ^ 2 ^ n * 2 ^ 2 ^ n + 2 ^ 2 ^ n * 1 - 2 ^ 2 ^ n - 1          := by exact rfl
      _ = 2 ^ (2 ^ Nat.succ n) - 1                                       := by simp [Nat.sub_self, ←Nat.pow_two, ←Nat.pow_mul', ←Nat.pow_succ'] -- keep
      _ = F (Nat.succ n) - 2                                             := by exact rfl -- keep

lemma coprime_iff_divisors_one (k n : ℕ) : Nat.Coprime k n ↔ ∀ m, m ∣ k ∧ m ∣ n → m = 1 :=
  ⟨λ k_n_coprime _ => (λ hm => Nat.eq_one_of_dvd_coprimes k_n_coprime hm.1 hm.2),
   λ h => h (Nat.gcd k n) ⟨Nat.gcd_dvd_left k n, Nat.gcd_dvd_right k n⟩⟩

/-- Fermat numbers are pairwise coprime -/
-- (2) We will show that any two Fermat numbers are relatively prime; ...
-- (5) ... from which our assertion follows immediately
lemma F_coprime (k n : ℕ) (k_ne_n: k ≠ n) : Nat.Coprime (F k) (F n) := by
  rw [coprime_iff_divisors_one]

  -- (6) Indeed, if m is a divisor of, say, Fk and Fn ...
  intro m ⟨m_dvd_Fk, m_dvd_Fn⟩

  -- (7) ... (k < n) ...
  wlog k_lt_n : k < n
  · exact this n k k_ne_n.symm m m_dvd_Fn m_dvd_Fk (lt_of_le_of_ne (le_of_not_gt k_lt_n) k_ne_n.symm)
  · have m_dvd_PFk  :  m ∣ (∏ k in range n, F k)          := Nat.dvd_trans m_dvd_Fk (dvd_prod_of_mem F (mem_range.mpr k_lt_n))
    have m_dvd_diff :  m ∣ (F n - (∏ k in range n, F k))  := Nat.dvd_sub' m_dvd_Fn m_dvd_PFk

    -- (8) ... then m divides 2 ...
    have m_dvd_two  :  m ∣ 2 := by
      have two_through_fermat : 2 = (F n - (∏ k in range n, F k)) := by
        simp [F_prod_form, Nat.sub_sub_self (F_ge_two n)]
      rw [two_through_fermat]
      exact m_dvd_diff

    -- (9) ... and hence m = 1 or 2.
    have m_ne_zero : m ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.succ_ne_zero 1) m_dvd_two
    have m_le_two : m ≤ 2 := Nat.le_of_dvd (Nat.two_pos) m_dvd_two

    -- (10) But m = 2 is impossible ...
    have m_ne_two : m ≠ 2 := by
      by_contra m_eq_two
      have Fn_not_odd : ¬Odd (F n) := Nat.even_iff_not_odd.mp (even_iff_two_dvd.mpr (m_eq_two ▸ m_dvd_Fn))
      exact Fn_not_odd (F_odd n)

    exact Nat.eq_of_lt_succ_of_not_lt (lt_of_le_of_ne m_le_two m_ne_two) (Nat.not_lt.mpr (Nat.one_le_iff_ne_zero.mpr m_ne_zero))

/-- Proof of the infinitude of primes --/
-- (3) ... hence there must be infinitely many primes.
theorem infinitude_of_primes : ∃ P : ℕ → ℕ, Injective P ∧ ∀ k, (P k).Prime := by {
  choose P P_prime P_dvd_fermat using fun n ↦ Nat.exists_prime_and_dvd (ne_of_gt (F_ge_two n))
  have P_inj : Injective P := by
    intros m n Pm_eq_Pn
    have Pm_dvd_gcd : P m ∣ Nat.gcd (F m) (F n) := Nat.dvd_gcd (P_dvd_fermat m) (Pm_eq_Pn ▸ P_dvd_fermat n)
    by_contra m_ne_n
    have Pm_dvd_one : P m ∣ 1 := F_coprime m n m_ne_n ▸ Pm_dvd_gcd
    exact Nat.Prime.ne_one (P_prime m) (Nat.dvd_one.mp Pm_dvd_one)
  exact ⟨P, P_inj, P_prime⟩
}

/-- Proof of the standardized infinitude of primes -/
theorem infinitude_primes_standardized : { p : ℕ | Nat.Prime p}.Infinite := by {
  obtain ⟨P, P_inj, P_im_prime⟩ := infinitude_of_primes
  exact Set.infinite_of_injective_forall_mem P_inj P_im_prime
}

end GoldbachIfinitudePrimes
