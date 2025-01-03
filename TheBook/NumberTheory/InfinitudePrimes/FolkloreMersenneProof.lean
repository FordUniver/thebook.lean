import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Set.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace FolkloreMersenneInfinitudePrimes


-- Let q be a prime dividing 2^p − 1
lemma mersenne_prime_dvd_gt (p q : ℕ) [p_prime: Fact (Nat.Prime p)] [q_prime : Fact (Nat.Prime q)]
    (h : q ∣ 2^p - 1) : p < q := by

  -- so we have 2^p ≡ 1 (mod q)
  have two_pow_p_eq_one_mod_q : 2^p ≡ 1 [MOD q] :=
    ((λ x ↦ (Nat.modEq_iff_dvd' x).mpr) (Nat.one_le_two_pow) h).symm

  -- Since p is prime, this means that the element 2 has order p in the multiplicative group
  -- Zq \ {0} of the field Zq
  have two_pow_p_eq_one := ((ZMod.eq_iff_modEq_nat q).mpr two_pow_p_eq_one_mod_q)
  rw [Nat.cast_pow, Nat.cast_one] at two_pow_p_eq_one
  have order_two_eq_p := orderOf_eq_prime two_pow_p_eq_one (by apply sub_eq_zero.not.mp; norm_num)

  -- This group has q − 1 elements. By Lagrange’s theorem we know that the order of every element
  -- divides the size of the group, that is, we have p | q − 1
  have two_ne_zero : (2 : ZMod q) ≠ 0 := by
    by_contra contra
    have q_lq_two : q ≤ 2 :=
      (Nat.Prime.dvd_factorial q_prime.out).mp ((ZMod.natCast_zmod_eq_zero_iff_dvd 2 q).mp contra)
    have q_gt_two : q > 2 :=
      Nat.lt_of_le_of_ne
        (Nat.Prime.two_le q_prime.out)
        (Odd.ne_two_of_dvd_nat
          (Nat.Even.sub_odd
            (Nat.one_le_two_pow)
            (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.Prime.ne_zero p_prime.out)))
            (Exists.intro Nat.zero rfl)) h).symm
    exact (Nat.not_lt.mpr q_lq_two) q_gt_two

  have p_dvd_q_minus_1 : p ∣ (q - 1) := order_two_eq_p ▸ (ZMod.orderOf_dvd_card_sub_one two_ne_zero)

  -- and hence p < q.
  exact Nat.lt_of_le_pred
    (Nat.Prime.pos q_prime.out)
    (Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.Prime.two_le q_prime.out)) p_dvd_q_minus_1)

theorem infinitude_of_primes : { p : ℕ | Nat.Prime p}.Infinite := by
  -- Suppose P is finite and p is the largest prime.
  by_contra contra
  have : Fintype { p : ℕ | Nat.Prime p} := Set.Finite.fintype (Set.not_infinite.mp contra)
  let P := { p : ℕ | Nat.Prime p}.toFinset
  let P_nonenmpty : P.Nonempty := (Set.nonempty_of_mem (Set.mem_toFinset.mpr Nat.prime_two))
  let p := Finset.max' P P_nonenmpty
  have p_in_P : p ∈ P := Finset.max'_mem P P_nonenmpty
  have p_prime : Nat.Prime p := by simp [P] at p_in_P; exact p_in_P

  -- 2^p - 1 would have a prime divisor large than p
  have two_pow_p_minus_one_ne_one : 2^p - 1 ≠ 1 :=
    Nat.ne_of_gt (Nat.lt_sub_of_add_lt
      ((@Nat.size_le 2 p).mp (Eq.trans_le (@Nat.size_pow 1) (Nat.Prime.two_le p_prime))))
  let ⟨q, q_prime, q_dvd⟩ := Nat.exists_prime_and_dvd two_pow_p_minus_one_ne_one
  have q_gt_p : q > p := @mersenne_prime_dvd_gt p q (Fact.mk p_prime) (Fact.mk q_prime) q_dvd

  -- But this is a contradiciton
  have q_lt_p : q ≤ p := Finset.le_max' P q (Set.mem_toFinset.mpr q_prime)
  exact Nat.lt_irrefl p (Nat.lt_of_lt_of_le q_gt_p q_lt_p)

end FolkloreMersenneInfinitudePrimes
