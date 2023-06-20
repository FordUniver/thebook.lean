--Infinitude of the primes

import data.nat.prime
import algebra.big_operators.basic
import algebra.big_operators.order
import tactic


--First proof:

#check nat.exists_infinite_primes -- mathlib version

--Mathematics in Lean version
lemma two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  cases m, contradiction,
  cases m, contradiction,
  repeat { apply nat.succ_le_succ },
  apply zero_le,
end

example {n : nat} (h : 2 ≤ n) :
  ∃ p : nat, p.prime ∧ p ∣ n :=
  by {--direct library search fails
      have alt : n ≠ 1 := by {linarith,},
      exact nat.exists_prime_and_dvd alt, --here the search will work
      }

lemma exists_prime_factor {n : nat} (h : 2 ≤ n) :
  ∃ p : nat, p.prime ∧ p ∣ n :=
begin
  by_cases np : n.prime,
  { use [n, np, dvd_rfl], },
  induction n using nat.strong_induction_on with n ih,
  dsimp at ih,
  rw nat.prime_def_lt at np,
  push_neg at np,
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩,
  have : m ≠ 0,
  { intro mz,
    rw [mz, zero_dvd_iff] at mdvdn,
    linarith },
  have mgt2 : 2 ≤ m := two_le this mne1,
  by_cases mp : m.prime,
  { use [m, mp, mdvdn] },
  rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩,
  use [p, pp, pdvd.trans mdvdn],
end

theorem primes_infinite : ∀ n, ∃ p > n, nat.prime p :=
begin
  intro n,
  have : 2 ≤ nat.factorial (n + 1) + 1,
  { apply nat.succ_le_succ,
    exact nat.succ_le_of_lt (nat.factorial_pos _) },
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  refine ⟨p, _, pp⟩,
  show p > n,
  by_contradiction ple, push_neg at ple,
  have : p ∣ nat.factorial (n + 1),
  { apply nat.dvd_factorial,
    apply pp.pos,
    linarith },
  have : p ∣ 1,
  { convert nat.dvd_sub' pdvd this, simp },
  show false,
  have := nat.le_of_dvd zero_lt_one this,
  linarith [pp.two_le],
end

--Infinity in the laguage of finsets, still the Math in Lean version
open finset
open_locale big_operators

theorem primes_infinite' : ∀ (s : finset nat), ∃ p, nat.prime p ∧ p ∉ s :=
begin
  intro s,
  by_contradiction h,
  push_neg at h,
  set s' := s.filter nat.prime with s'_def,
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.prime,
  { intro n,
    simp [s'_def],
    apply h },
  have : 2 ≤ (∏ i in s', i) + 1,
  { apply nat.succ_le_succ,
    apply nat.succ_le_of_lt,
    apply prod_pos,
    intros n ns',
    apply (mem_s'.mp ns').pos },
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  have : p ∣ (∏ i in s', i),
  { apply dvd_prod_of_mem,
    rw mem_s',
    apply pp },
  have : p ∣ 1,
  { convert nat.dvd_sub' pdvd this, simp },
  show false,
  have := nat.le_of_dvd zero_lt_one this,
  linarith [pp.two_le],
end




-- Second proof 

def FermatPrimes_prod : ℕ → ℕ
| 0 := 3
| (n+1) := ((FermatPrimes_prod n) + 2)*(FermatPrimes_prod n)

lemma powLem (n : nat) : 1 ≤ 2 ^ 2 ^ (n + 1) :=
  by {exact nat.one_le_pow' (2 ^ (n + 1)) 1}

lemma FermaG2 (n : nat) : 0 < FermatPrimes_prod n :=
  by {induction n with n ih,
      simp [FermatPrimes_prod],
      rw [FermatPrimes_prod],
      rw right_distrib,
      calc
      0 < 1*1   : by {apply nat.mul_pos, norm_num, norm_num}
      ... ≤ (FermatPrimes_prod n * FermatPrimes_prod n) * 1 :
        by {apply nat.le_mul_of_pos_left,
            exact mul_pos ih ih}
      ... ≤ (FermatPrimes_prod n * FermatPrimes_prod n) + 2 * FermatPrimes_prod n :
        by {simp},}

lemma tmp (n : nat) (h : 0 < n) : (n + 1)*(n - 1) = n^2 - 1^2 :=
 by {rw [add_one_mul, mul_tsub, mul_one, tsub_add_tsub_cancel, sq],
     simp, rw ← pow_two,
     exact nat.le_self_pow two_ne_zero n,
     exact nat.succ_le_iff.2 ‹0 < n›, }

lemma tmp2 (n : nat) (h : 0 < n): n - 1 + 2 = n + 1 :=
    by {linarith}

theorem FermatPrimes_prod_closedForm (n : nat) : FermatPrimes_prod n + 2 = 2^(2^(n+1)) + 1 :=
  by {induction n with n ih,
      simp [FermatPrimes_prod], norm_num, 
      rw [FermatPrimes_prod],
      simp [ih],
      have ih_aux : FermatPrimes_prod n = 2 ^ 2 ^ (n + 1) - 1 :=
        by {have h1 : 1 ≤ 2 ^ 2 ^ (n + 1) := powLem n,
            have h2 : 0 < FermatPrimes_prod n := FermaG2 n,
            linarith,},
      rw ih_aux,
      have pain : n.succ = n + 1 := by {exact rfl},
      rw pain,
      calc
      (2 ^ 2 ^ (n + 1) + 1) * (2 ^ 2 ^ (n + 1) - 1) + 2 = (2 ^ 2 ^ (n + 1))^ 2 - 1^2 + 2  : 
        by {simp,
        have h1 : 1 ≤ 2 ^ 2 ^ (n + 1) := powLem n,
        apply tmp (2 ^ 2 ^ (n + 1)),
        linarith,}
      ... = (2 ^ 2 ^ (n + 1))^ 2 + 1  :
          by {simp, 
              have pain2 : 0 < 2 ^ 2 ^ (n + 1) := by norm_num,
              rw tmp2 ((2 ^ 2 ^ (n + 1)) ^ 2) (pow_pos pain2 2),}
      ... = (2 ^ (2 ^ (n + 1)) * 2 ^ (2 ^ (n + 1))) + 1  :
          by {simp, rw sq,}
      ... = (2 ^ (2*(2 ^ (n + 1) ))) + 1  :
          by {simp, rw two_mul, exact tactic.ring.pow_add_rev 2 (2 ^ (n + 1)) (2 ^ (n + 1))}
      ... = (2 ^ 2 ^ (n + 1 + 1) ) + 1  :
          by {simp,
              have pain3 : 2 * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) :=
                by {rw add_comm (n+1) 1,
                    nth_rewrite 0 ← pow_one 2,
                    rw pow_add 2 1 (n+1),},
              rw pain3,},}


lemma FermatOdd (n : nat) : ¬(2 ∣ (FermatPrimes_prod n)+2) :=
  by {intro C,
      rw FermatPrimes_prod_closedForm n at C,
      have l : 2 ∣ 2^(2^(n+1)) :=
        by {nth_rewrite 0 ← pow_one 2,
            have pain : 1 < 2 := by {norm_num},
            rw (nat.pow_dvd_pow_iff_le_right  pain),
            apply nat.one_le_pow,
            norm_num,},
      have l2 : 2 ∣ 1 :=
        by {rw ← nat.dvd_add_right l, exact C,},
      have pain2 : 0<1 := by {norm_num},
      have c : 2 ≤ 1 := by {exact nat.le_of_dvd pain2 l2,},
      linarith,}


lemma FermatDiv (n m : nat) (O : n < m) :
((FermatPrimes_prod n)+2) ∣ (FermatPrimes_prod m) :=
  by {induction m with m ih,
      apply by_contra, intro A, linarith,
      rw FermatPrimes_prod,
      apply lt_by_cases n m,
      {intro A,
      specialize ih A,
      exact dvd_mul_of_dvd_right ih (FermatPrimes_prod m + 2)},
      {intro A,
      rw A,
      exact dvd.intro (FermatPrimes_prod m) rfl},
      {intro A,
       apply by_contra, intro C,
       have pain : m.succ = m + 1 := by {exact rfl},
       rw pain at O,
       linarith,},}
                                      

lemma FermatCoprime_prelude (n m d : nat) (diff : n ≠ m) (D : 1 < d)
(h : d ∣ ((FermatPrimes_prod n)+2)) (H : d ∣ ((FermatPrimes_prod m)+2)) : d = 2 :=
  by {apply lt_by_cases n m,
      {intro ineq,
       have hd : d ∣ (FermatPrimes_prod m) := by {apply dvd_trans,
                                                  exact h,
                                                  exact FermatDiv n m ineq,},
       have dd2 : d ∣ 2 := by {exact (nat.dvd_add_right hd).mp H},
       have dl2 : d ≤ 2 := by {apply nat.le_of_dvd, norm_num, exact dd2,},
       linarith,},
       {intro A, by_contra, exact diff A,},
       {intro ineq,
       have hd : d ∣ (FermatPrimes_prod n) := by {apply dvd_trans,
                                                  exact H,
                                                  exact FermatDiv m n ineq,},
       have dd2 : d ∣ 2 := by {exact (nat.dvd_add_right hd).mp h},
       have dl2 : d ≤ 2 := by {apply nat.le_of_dvd, norm_num, exact dd2,},
       linarith,},}


theorem InfinityViaFermat (n : nat) :
∃ (L : ℕ → ℕ), ((∀ k, (k ≤ n) → (L k).prime) ∧ 
(∀ k, (k ≤ n) → (∀ q, (q ≤ n) → (((L k) = (L q)) → k = q))) ∧ 
(∀ k, (k ≤ n) → ((L k) ∣ ((FermatPrimes_prod k)+2)))) :=
  by {induction n with n ih,
      have base : ∃ p : nat, p.prime ∧ p ∣ 5 :=
        by {apply exists_prime_factor, linarith,},
      cases base with p hp,
      use (λ k, p),
      split,
      intros k A,
      exact hp.1,
      split,
      intros k hk q hk eq, linarith,
      intros k hk,
      have H : k = 0 := by {linarith}, rw H, simp [FermatPrimes_prod],
      norm_num, exact hp.2,
      --base done
      cases ih with L AL,
      have base : ∃ p : nat, p.prime ∧ p ∣ ((FermatPrimes_prod (n+1)) +2) :=
        by {apply exists_prime_factor, linarith,},
      cases base with p hp,
      use (λ k, if k ≤ n then L k else p),
      split,
      have pain : n.succ = n + 1 := by {exact rfl}, rw pain,
      intros k kineq,
      apply lt_by_cases k (n+1),
      intro C1, have C1' : k ≤ n := by {linarith},
      rw if_pos C1',
      exact AL.1 k C1',
      intro C2, have C2' : ¬(k ≤ n) := by {linarith},
      rw if_neg C2',
      exact hp.1,
      intro C2, have C2' : ¬(k ≤ n) := by {linarith},
      rw if_neg C2',
      exact hp.1,
      --first property of the map done
      split,
      have pain : n.succ = n + 1 := by {exact rfl}, rw pain,
      intros k kineq q qineq,
      apply lt_by_cases k (n+1),
      intro C1, have C1' : k ≤ n := by {linarith},
      rw if_pos C1',
      apply lt_by_cases q (n+1),
      intro C2, have C2' : q ≤ n := by {linarith},
      rw if_pos C2',
      exact AL.2.1 k C1' q C2',
      intro C3, have C3' : ¬(q ≤ n) := by {linarith},
      rw if_neg C3',
      intro A, by_contra,
      have Contra : p ∣ (FermatPrimes_prod k + 2) :=
        by {rw ← A, exact AL.2.2 k C1',},
      have pain1 : k ≠ n+1 := by {linarith},
      have Contra2 : p = 2 := 
        FermatCoprime_prelude k (n+1) p pain1 (nat.prime.one_lt hp.1) Contra hp.2,
      rw Contra2 at Contra, exact FermatOdd k Contra,
      intro C4, have C4' : ¬(q ≤ n) := by {linarith}, --same as in the previous goal
      rw if_neg C4',
      intro A, by_contra,
      have Contra : p ∣ (FermatPrimes_prod k + 2) :=
        by {rw ← A, exact AL.2.2 k C1',},
      have pain1 : k ≠ n+1 := by {linarith},
      have Contra2 : p = 2 :=
      FermatCoprime_prelude k (n+1) p pain1 (nat.prime.one_lt hp.1) Contra hp.2,
      rw Contra2 at Contra, exact FermatOdd k Contra,
      intro C5, have C5' : ¬(k ≤ n) := by {linarith},
      rw if_neg C5',
      apply lt_by_cases q (n+1),
      intro C6, have C6' : q ≤ n := by {linarith},
      rw if_pos C6',
      intro A, by_contra,
      have Contra : p ∣ (FermatPrimes_prod q + 2) :=
        by {rw A, exact AL.2.2 q C6',},
      have pain1 : q ≠ n+1 := by {linarith},
      have Contra2 : p = 2 :=
        FermatCoprime_prelude q (n+1) p pain1 (nat.prime.one_lt hp.1) Contra hp.2,
      rw Contra2 at Contra, exact FermatOdd q Contra,
      intro C7, have C7' : ¬(q ≤ n) := by {linarith},
      rw if_neg C7',
      intro o, linarith,
      intro C8, have C8' : ¬(q ≤ n) := by {linarith},
      rw if_neg C8', by_contra, linarith,
      intro C9, have C9' : ¬(q ≤ n) := by {linarith},
      rw if_neg C9', by_contra, linarith,
      --last property of the function
      have pain : n.succ = n + 1 := by {exact rfl}, rw pain,
      intros k kineq,
      apply lt_by_cases k (n+1),
      intro C1, have C1' : k ≤ n := by {linarith},
      rw if_pos C1',
      exact AL.2.2 k C1',
      intro C2, have C2' : ¬(k ≤ n) := by {linarith},
      rw if_neg C2',
      rw C2, exact hp.2,
      intro C2, have C2' : ¬(k ≤ n) := by {linarith},
      rw if_neg C2',
      by_contra, linarith, --takes time to load, but accomplished it is !
      } 