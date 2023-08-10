--Pigeonhole principle (Chapter 27)

import data.finset.basic
import data.finset.card

import data.nat.gcd.basic
import data.nat.parity

import tactic


open finset

-- Pigeonhole principle

lemma my_pigeonhole {α β : Type*} [decidable_eq α] [decidable_eq β]
        (n : nat) :
        ∀(S : finset α), ∀(T : finset β),
        ∀(f : α → β), ((∀(s : α), s∈S → f s ∈ T) ∧  
        (T.card = n) ∧ (n < S.card)) →  
        ∃a,∃b, a∈S ∧ b∈S ∧ (a≠b) ∧ (f a = f b) :=
by {induction n with n ih,
      intros S T f,
      rintros ⟨map, tec, size⟩,    
      rw card_pos at size,
      cases size with s sS,
      specialize map s sS,
      rw card_eq_zero at tec,
      rw tec at map,
      by_contra, exact not_mem_empty (f s) map, --base done
      intros S T f,
      rintros ⟨map, tec, size⟩,
      -- take a t in T
      have tT_pred : ∃t,t∈T :=
        by {have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have tmp : 0 < T.card := by {linarith,}, rw card_pos at tmp,
            exact tmp,},
      cases tT_pred with t tT,
      by_cases (∃a, a∈S ∧ f a = t), -- is there an antecdant of t ?
      rcases h with ⟨a, aS, fat⟩,
      by_cases (∃b, b∈S ∧ f b = t ∧ a ≠ b), --is there another ?
      rcases h with ⟨b, bS, fbt, bna⟩, 
      use a, use b,rw ← fat at fbt, rw eq_comm at fbt,
      exact ⟨aS, bS, bna, fbt⟩,  
      --exactly one antecedant
      push_neg at h,
      let S' := erase S a,
      let T' := erase T t,
      have map' : ∀(s : α), s∈S' → f s ∈ T' :=
        by {intros s sS,
            dsimp [T'], dsimp [S'] at sS,
            rw mem_erase at *,
            split,
            by_contra c,
            specialize h s sS.2 c,
            rw eq_comm at h,
            exact sS.1 h,
            exact map s sS.2,},
      have sizeT' : T'.card = n :=
        by {have l : T'.card = T.card - 1:= by {apply card_erase_of_mem,
                                                exact tT,},
            have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ T.card := by {have tmp : T.nonempty :=
                                             by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      have sizeS' : n < S'.card :=
        by {have l : S'.card = S.card - 1:= by {apply card_erase_of_mem,
                                                exact aS,},
            have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ S.card := by {have tmp : T.nonempty :=
                                            by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      specialize ih S' T' f ⟨map', sizeT', sizeS'⟩,  
      have inS : S' ⊆ S := by {dsimp [S'], refine erase_subset a S,},
      cases ih with a A, cases A with b B, rcases B with ⟨aS', bS', anb, feq⟩, 
      use a, use b, exact ⟨inS aS', inS bS', anb, feq⟩,
      -- no antecedants
      push_neg at h,
      let T' := erase T t,
      have map' : ∀(s : α), s∈S → f s ∈ T' :=
        by {intros s sS,
            dsimp [T'],
            rw mem_erase at *,
            split,
            exact h s sS,
            exact map s sS,},
      have sizeT' : T'.card = n :=
        by {have l : T'.card = T.card - 1:= by {apply card_erase_of_mem,
                                                exact tT,},
            have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ T.card := by {have tmp : T.nonempty :=
                                            by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      have sizeS : n < S.card :=
        by {have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ S.card := by {have tmp : T.nonempty :=
                                            by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      specialize ih S T' f ⟨map', sizeT', sizeS⟩, 
      exact ih,
      }


-- Partitions and cardinals, as prelude to generalized pigeonhole

lemma erase_union_singleton {α : Type*} [decidable_eq α]
                            (S : finset α) (s : α) (h : s ∈ S) :
                            S = (erase S s) ∪ (singleton s) :=
      by {ext x, simp, split,
          intro xS, by_cases (x = s), exact or.inr h, apply or.inl, exact ⟨h,xS⟩,
          intro A, cases A, exact A.2, rw ← A at h, exact h,}



open_locale big_operators

lemma card_disj_bUnion {α β : Type*} [decidable_eq α] [decidable_eq β] (n : nat) :
                       ∀(I : finset α), ∀(S : finset β), ∀(fam : α → finset β),
                       ((∀i,∀j, (i∈I ∧ j∈I ∧ i≠j) → disjoint (fam i) (fam j)) ∧ (I.card = n) ∧ 
                       (S = finset.bUnion I fam)) → 
                       (S.card = ∑ i in I, (fam i).card) :=
      by {induction n with n ih,
          intros I S fam, rintros ⟨D,size,eq⟩, 
          simp at size, rw size at eq, rw size,
          rw bUnion_empty at eq,
          rw finset.sum_empty, simp, exact eq, -- base done
          intros I S fam, rintros ⟨D,size,eq⟩,
          have pain : n.succ = n+1 := by {refl},
          have iI : ∃i,i∈I :=
            by {have tmp : 0 < I.card := by {linarith,}, rw card_pos at tmp, exact tmp,},
          cases iI with i iI,
          let I' := erase I i,
          have sizeI' : I'.card = n :=
            by {have l : I'.card = I.card - 1:= by {apply card_erase_of_mem,
                                                exact iI,},
                have pain2 : 1 ≤ I.card := by {have tmp : I.nonempty := by {use i, exact iI,},
                                           rw ← card_pos at tmp,
                                           linarith,},
                rw pain at size,
                linarith,},
          have l_1 : disjoint I' (singleton i) := by {simp,},
          have l_2 : I = disj_union I' (singleton i)  l_1 :=
            by {have tmp : disj_union I' (singleton i)  l_1 = I' ∪ (singleton i) :=
                  by {exact disj_union_eq_union I' {i} l_1,},
                rw tmp, apply erase_union_singleton, exact iI,},
          rw l_2, rw sum_disj_union, rw sum_singleton,
          have l_3 : disjoint (finset.bUnion I' fam) (fam i) :=
            by {rw disjoint_bUnion_left, intros j jI,
                have tmp : i≠j := by {dsimp [I'] at jI, exact (ne_of_mem_erase jI).symm,},
                have tmp2 : j∈I := by {dsimp [I'] at jI, exact mem_of_mem_erase jI,}, 
                specialize D j i ⟨tmp2, iI, tmp.symm⟩, exact D,},
          have l_4 : S = disj_union (finset.bUnion I' fam) (fam i) l_3:=
            by {rw disj_union_eq_union,
                ext x, split, intro xS, rw eq at xS, rw mem_bUnion at xS,
                cases xS with i' i'I, cases i'I with i'I xfi', by_cases (i' = i),
                rw mem_union, rw ← h, exact or.inr xfi',
                rw mem_union, apply or.inl, rw mem_bUnion, use i', dsimp[I'], rw mem_erase,
                exact ⟨⟨h,i'I⟩,xfi'⟩,
                rw mem_union, intro H, cases H, rw mem_bUnion at H, dsimp[I'] at H,
                cases H with a H', cases H' with H' H'',
                rw eq, rw mem_bUnion, use a, split, exact mem_of_mem_erase H', exact H'',
                rw eq, rw mem_bUnion, use i, exact ⟨iI,H⟩,},
          rw l_4,
          rw card_disj_union,
          have induc : (I'.bUnion fam).card = ∑ (x : α) in I', (fam x).card :=
            by {apply ih, split,
            intros a b, rintros ⟨aI',bI',anb⟩, dsimp [I'] at aI', dsimp [I'] at bI',
            specialize D a b ⟨mem_of_mem_erase aI', mem_of_mem_erase bI', anb⟩, exact D, 
            split, exact sizeI', refl,},
          linarith,
          }


-- Generalized peigeonhole

lemma partition_preimages {α β : Type*} [decidable_eq α] [decidable_eq β] (r : nat)
        (S : finset α) (T : finset β) (f : α → β) (map : ∀(s : α), s∈S → f s ∈ T) :
        (S = finset.bUnion T (λ t, (S.filter (λ x, f x = t))) ∧
        (∀i,∀j, (i∈T ∧ j∈T ∧ i≠j) → disjoint (S.filter (λ x, f x = i)) (S.filter (λ x, f x = j)))) :=
        by {split, ext x, split, intro xS, rw mem_bUnion,
            use f x, split, exact map x xS, rw mem_filter, split, exact xS, refl,
            rw mem_bUnion, intro A, cases A with t A, cases A with H A, rw mem_filter at A,
            exact A.1,
            intros i j, rintro ⟨iT,jT,inj⟩, rw disjoint_iff_ne, intros a ai b bj,
            by_contra C, rw mem_filter at *, rw C at ai, have c : i = j :=
              by {rw eq_comm, apply eq.trans bj.2.symm, exact ai.2,},
            exact inj c, 
            }

lemma sum_bound {α : Type*} [decidable_eq α] (n r: nat) :
        ∀(S : finset α), ∀(f : α → nat), (S.card = n) → (∀ (s : α), s ∈ S → f s ≤ r) → 
        (∑ s in S, (f s) ≤ r*n) :=
        by {induction n with n ih,
            intros S f Sempty map, simp at Sempty, rw Sempty, rw sum_empty, linarith,
            have pain : n.succ = n+1 := by {refl}, rw pain,
            intros S f Ssize map,
            have sS : ∃s,s∈S :=
              by {have tmp : 0 < S.card := by {linarith,}, rw card_pos at tmp, exact tmp,},
            cases sS with s sS,
            let S' := erase S s,
            have sizeS' : S'.card = n :=
              by {have l : S'.card = S.card - 1:= by {apply card_erase_of_mem,
                                                  exact sS,},
                  have pain2 : 1 ≤ S.card := by {have tmp : S.nonempty :=
                                                  by {use s, exact sS,},
                                            rw ← card_pos at tmp,
                                            linarith,},
                  linarith,},
            have l_1 : disjoint S' (singleton s) := by {simp,},
            have l_2 : S = disj_union S' (singleton s)  l_1 :=
              by {have tmp : disj_union S' (singleton s)  l_1 = S' ∪ (singleton s) :=
                    by {exact disj_union_eq_union S' {s} l_1,},
                  rw tmp, apply erase_union_singleton, exact sS,},
            rw l_2, rw sum_disj_union, rw sum_singleton,
            have map' : ∀ (s : α), s ∈ S' → f s ≤ r :=
              by {intros a aS', exact map a (mem_of_mem_erase aS'),},
            specialize ih S' f sizeS' map',
            rw mul_add, rw mul_one, specialize map s sS, linarith,}

lemma sum_card_bound {α : Type*} [decidable_eq α] (r : nat)
        (S : finset α) (f : α → nat) (bound : r*S.card < ∑ s in S, (f s)) :
        ∃s,s∈S ∧ (r < f s) :=
        by {by_contra' C,
            have b1 : ∑ s in S, (f s) ≤ r*S.card :=
              by {apply sum_bound, refl, exact C,},
            linarith,}

lemma my_generalized_pigeonhole {α β : Type*} [decidable_eq α] [decidable_eq β] (r : nat)
        (S : finset α) (T : finset β) (f : α → β) (map : ∀(s : α), s∈S → f s ∈ T)  
        (ineq : r*T.card < S.card) : 
        ∃a, (a∈T) ∧ (r < (S.filter (λ x, f x = a)).card) :=
        by {let n := T.card, have tec : T.card = n := by {refl,},
            rw [card_disj_bUnion n T S (λ t, (S.filter (λ x, f x = t)))
                (⟨(partition_preimages r S T f map).2,tec,(partition_preimages r S T f map).1⟩)]
                at ineq,
            by_contra' C,
            have L1 : (∑ t in T, ((filter (λ (x : α), f x = t) S).card) ≤ r*n) :=
              by {exact sum_bound n r T (λ t, ((filter (λ (x : α), f x = t) S).card)) tec C,},
            simp at ineq, rw tec at ineq, linarith [ineq, C],
            }


-- 1. Numbers

-- Claim 1

lemma succ_coprime (n m : nat) (h : n = m+1) : nat.coprime n m :=
  by {rw h, rw nat.coprime_self_add_left, exact nat.coprime_one_left m,}

example (n : nat) (h : 1≤n) : ∀A, A ∈ (powerset_len (n+1) (image (λ x, x+1) (range (2*n)))) →
        ∃a,∃b, a∈A ∧ b∈A ∧ (a≠b) ∧ (nat.coprime a b) :=
        by {intros A Adef, rw mem_powerset_len at Adef,
            have Lem1 : ∃a,∃b, a∈A ∧ b∈A ∧ (a≠b) ∧ ((λ (x : ℕ), (x+1) / 2) a =
                        (λ (x : ℕ), (x+1) / 2) b):=
              by {apply my_pigeonhole n A (image (λ x, x+1) (range (n))) (λ x, (x+1) / 2),
                  split, intros m mA, simp, use (((m+1) / 2) - 1),
                  have tec1 : m ∈ image (λ (x : ℕ), x + 1) (range (2 * n)) :=
                                                by {exact Adef.1 mA,},
                  simp at tec1, rcases tec1 with ⟨a,a1,a2⟩,
                  have tec2 : 1≤(m+1)/2 := by {rw nat.le_div_iff_mul_le',
                                              linarith, norm_num,},
                  split, rw tsub_lt_iff_right tec2, rw nat.div_lt_iff_lt_mul', 
                  linarith, norm_num,
                  linarith,
                  split,
                  rw card_image_of_injective, exact card_range n, dsimp [function.injective],
                  intros a b aeb, linarith,
                  rw Adef.2, linarith,},
            rcases Lem1 with ⟨a, b, aA, bA, anb, abeq⟩, simp at abeq,
            use a, use b, split, exact aA, split, exact bA, split, exact anb,
            have Lem2 : (a+1)%2 ≠ (b+1)%2 := by {by_contra C,
                                                 have tec : a+1 = b+1 :=
                                                  by {rw ← nat.div_add_mod (a+1) 2,
                                                      rw ← nat.div_add_mod (b+1) 2,
                                                      linarith,},
                                                 apply anb, linarith,},
            apply lt_by_cases ((a + 1) % 2) 1,
            intro caselt, have tec1 : (a + 1) % 2 = 0 := by {exact nat.lt_one_iff.mp caselt,},
            have l1 : (b + 1) % 2 = 1 := by {apply lt_by_cases ((b + 1) % 2) 1, intro caltb,
                                             have tec2 : (b + 1) % 2 = 0 :=
                                              by {exact nat.lt_one_iff.mp caltb,},
                                             by_contra, apply Lem2, apply eq.trans tec1,
                                             exact tec2.symm,
                                             simp,
                                             intro C, by_contra,
                                             have pain : 0<2 := by {norm_num,},
                                             have tec3 : (b + 1) % 2 < 2 :=
                                              by {exact nat.mod_lt (b + 1) pain,},
                                             linarith,},
            have case_pre : a+1+1 = b+1 := by {rw ← nat.div_add_mod (a+1) 2,
                                               rw ← nat.div_add_mod (b+1) 2,
                                               linarith,},
            have case : a+1 = b := by {linarith,},
            rw nat.coprime_comm, rw eq_comm at case, exact succ_coprime b a case,
            intro caseq,
            have l1 : (b + 1) % 2 = 0 := by {apply lt_by_cases ((b + 1) % 2) 1, intro caltb,
                                             have tec2 : (b + 1) % 2 = 0 :=
                                              by {exact nat.lt_one_iff.mp caltb,},
                                             exact tec2, intro caoneb,
                                             by_contra C, apply Lem2, apply eq.trans caseq,
                                             exact caoneb.symm,
                                             intro C, by_contra,
                                             have pain : 0<2 := by {norm_num,},
                                             have tec3 : (b + 1) % 2 < 2 :=
                                              by {exact nat.mod_lt (b + 1) pain,},
                                             linarith,},
            have case_pre : a+1 = b+1+1 := by {rw ← nat.div_add_mod (a+1) 2,
                                               rw ← nat.div_add_mod (b+1) 2,
                                               linarith,},
            have case : a = b+1 := by {linarith,},
            exact succ_coprime a b case,
            intro C, by_contra,
            have pain : 0<2 := by {norm_num,},
            have tec3 : (a + 1) % 2 < 2 := by {exact nat.mod_lt (a + 1) pain,},
            linarith,}

-- Claim 2

lemma ineq_tec  (n : nat): 2*n<2^(n+1) :=
    by {induction n with n ih, simp,
        have pain : n.succ = n+1 := by {refl,}, rw pain,
        rw pow_add, rw mul_add, rw pow_one, rw mul_one, rw mul_two, nth_rewrite 1 ← pow_one 2,
        have : 2^1≤2^(n+1) := by {apply pow_le_pow, norm_num, linarith,},
        linarith,}

lemma decompo_lemma (n : nat)  (a : nat) (aR : a ∈  (image (λ x, x+1) (range (2*n)))) :
    ∃(k : nat),∃(m : nat),(a=(2^k)*m)∧(m ∈ (image (λ x, x+1) (range (2*n))).filter (λ x, x%2 = 1)) :=
    by {let facSet : finset nat := (range (n+1)).filter (λ q, ∃p, a=(2^q)*p),
        have tec : facSet.nonempty :=
          by {dsimp [facSet], rw filter_nonempty_iff, use 0, split, simp, use a, simp,},
        let k := finset.max' facSet tec, use k,
        have l1 : k ∈ facSet := by {dsimp [k], exact finset.max'_mem facSet tec,},
        dsimp [facSet] at l1, rw mem_filter at l1, cases l1.2 with m eq, 
        use m, split, exact eq, simp, split,
        use (m-1), split,
        have tmp : m≤a := by {have tmp2 : 1 ≤ 2^k := by {exact nat.one_le_pow' k 1},
                              calc
                              m = 1*m : by {exact (one_mul m).symm}
                              ... ≤ (2^k)*m : by {exact mul_le_mul_right' tmp2 m}
                              ... = a : by {exact eq.symm,},},
        have tmp2 : a≤2*n := by {simp at aR, rcases aR with ⟨b, b1, b2⟩, linarith,},
        have pain : 1≤m := by {by_contra' c, have : m = 0 := by {linarith,}, rw this at eq,
                               simp at eq, simp at aR, rw eq at aR, rcases aR with ⟨b,b1,b2⟩,
                               linarith,},
        linarith,
        have pain : 1≤m := by {by_contra' c, have : m = 0 := by {linarith,}, rw this at eq,
                               simp at eq, simp at aR, rw eq at aR, rcases aR with ⟨b,b1,b2⟩,
                               linarith,},
        linarith,
        by_contra' C, rw  nat.mod_two_ne_one at C,
        have tec2 : m = 2*(m/2) := by {rw ← add_zero (2 * (m / 2)), rw ← C, exact (nat.div_add_mod m 2).symm,},
        rw tec2 at eq, rw ← mul_assoc at eq, nth_rewrite 1 ← pow_one 2 at eq, rw ← pow_add at eq,
        have con_pre : (k+1) ∈ facSet :=
          by {dsimp [facSet], rw mem_filter, split, rw mem_range,
              have tmp2 : a≤2*n := by {simp at aR, rcases aR with ⟨b, b1, b2⟩, linarith,},
              by_contra' C,
              have tmp3 : 2^(n+1)≤2^(k+1):= by {apply pow_mono, norm_num,exact C,},
              have tmp4 : a<2^(n+1) := by {have : 2*n<2^(n+1) := by {exact ineq_tec n,},
                                           linarith,},
              have con : 2 ^ (k + 1) * (m / 2) < 2 ^ (k + 1) := by {rw ←eq, linarith,},
              have con2 : 2 ^ (k + 1) ≤ 2 ^ (k + 1) * (m / 2) :=
                by {apply le_mul_of_one_le_right, norm_num,
                    have pain : 1≤m := by {by_contra' c, have : m = 0 := by {linarith,}, rw this at eq,
                               simp at eq, simp at aR, rw eq at aR, rcases aR with ⟨b,b1,b2⟩,
                               linarith,},
                    linarith,},
              apply absurd con, push_neg, exact con2,
              use m/2, exact eq,}, 
        have con_pre_2 : k+1≤ (finset.max' facSet tec) := by {apply le_max', exact con_pre,},
        dsimp [k] at con_pre_2, 
        linarith,
        }

lemma size_lemma (n : nat) : ((image (λ x, x+1) (range (2*n))).filter (λ x, x%2 = 1)).card = n :=
  by {apply card_eq_of_bijective (λ x xn, (2*x)+1),
      intros a aOR, simp at *, rcases aOR with ⟨⟨b,bl2n,boa⟩,aodd⟩,
      use a/2, split,
      have : a≤2*n := by {linarith,},
      rw ← nat.div_add_mod a 2 at this, rw aodd at this, linarith,
      nth_rewrite 1 ← nat.div_add_mod a 2, rw aodd,
      simp, intros i iln, split, exact iln, rw nat.add_mod, rw nat.mul_mod_right 2 i, simp,
      simp,}

open classical
open_locale classical

example (n : nat) : ∀A, A ∈ (powerset_len (n+1) (image (λ x, x+1) (range (2*n)))) →
        ∃a,∃b, a∈A ∧ b∈A ∧ (a≠b) ∧ (a ∣ b) :=
        by {intros A Adef,
            let f := λ (x : nat), if h : x ∈ (image (λ x, x+1) (range (2*n)))
                                  then nat.find (nat.find_spec (decompo_lemma n x h)) else 0,
            have pigeon : ∃a,∃b, a∈A ∧ b∈A ∧ (a≠b) ∧ (f a = f b) :=
              by {apply my_pigeonhole n A ((image (λ x, x+1) (range (2*n))).filter (λ x, x%2 = 1)),
                  split,
                  intros a aA,
                  have aR : a ∈ (image (λ x, x+1) (range (2*n))) :=
                    by {simp, rw mem_powerset_len at Adef, cases Adef, specialize Adef_left aA,
                        simp at Adef_left, exact Adef_left,},
                  dsimp [f], rw dif_pos aR, exact (nat.find_spec (nat.find_spec (decompo_lemma n a aR))).2,
                  split, exact size_lemma n,
                  rw mem_powerset_len at Adef, rw Adef.2, linarith,},
            rcases pigeon with ⟨a,b,aA,bA,anb,fafb⟩,
            rw mem_powerset_len at Adef,
            have l1 : a ∈ image (λ (x : ℕ), x + 1) (range (2 * n)) := Adef.1 aA,
            have l2 : b ∈ image (λ (x : ℕ), x + 1) (range (2 * n)) := Adef.1 bA,
            dsimp [f] at fafb, rw dif_pos l1 at fafb, rw dif_pos l2 at fafb,
            let ka := nat.find (decompo_lemma n a l1),
            let ma := nat.find (nat.find_spec (decompo_lemma n a l1)),
            let kb := nat.find (decompo_lemma n b l2),
            let mb := nat.find (nat.find_spec (decompo_lemma n b l2)),
            have L1 : a=(2^(ka))*(ma) := (nat.find_spec (nat.find_spec (decompo_lemma n a l1))).1,
            have L2 : (b=(2^(kb))*(mb)) := (nat.find_spec (nat.find_spec (decompo_lemma n b l2))).1,
            have L3 : ma = mb := by {exact fafb,},
            apply lt_by_cases ka kb,
            intro calb, use a, use b, split, exact aA, split, exact bA, split, exact anb,
            rw dvd_iff_exists_eq_mul_left, use 2^(kb-ka),
            rw L1, rw L2, rw ← mul_assoc, rw ← pow_add,
            have pain : kb - ka + ka = kb := by {have : ka ≤ kb := le_of_lt calb,
                                                  linarith,},
            rw pain, rw L3,
            intro caeb, use a, use b, split, exact aA, split, exact bA, split, exact anb,
            rw dvd_iff_exists_eq_mul_left, use 1, rw one_mul, rw L1, rw L2, rw L3, rw caeb,
            intro cbla, use b, use a, split, exact bA, split, exact aA, split, exact anb.symm,
            rw dvd_iff_exists_eq_mul_left, use 2^(ka-kb),
            rw L1, rw L2, rw ← mul_assoc, rw ← pow_add,
            have pain : ka - kb + kb = ka := by {have : kb ≤ ka := le_of_lt cbla,
                                                  linarith,},
            rw pain, rw L3,
            }

