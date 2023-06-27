--Pigeonhole principle and Double Counting

import data.finset.basic
import data.finset.card
import tactic


open finset

-- Pigeonhole principle

example {α β : Type*} [decidable_eq α] [decidable_eq β] (n : nat) :
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
            have pain2 : 1 ≤ T.card := by {have tmp : T.nonempty := by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      have sizeS' : n < S'.card :=
        by {have l : S'.card = S.card - 1:= by {apply card_erase_of_mem,
                                                exact aS,},
            have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ S.card := by {have tmp : T.nonempty := by {use t, exact tT,},
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
            have pain2 : 1 ≤ T.card := by {have tmp : T.nonempty := by {use t, exact tT,},
                                           rw ← card_pos at tmp,
                                           linarith,},
            linarith,},
      have sizeS : n < S.card :=
        by {have pain : n.succ = n+1 := by {refl}, rw pain at tec,
            have pain2 : 1 ≤ S.card := by {have tmp : T.nonempty := by {use t, exact tT,},
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
          have l_2 : I = disj_union I' (singleton i)  l_1 := by {have tmp : disj_union I' (singleton i)  l_1 = I' ∪ (singleton i) :=
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
                rw mem_union, apply or.inl, rw mem_bUnion, use i', dsimp[I'], rw mem_erase, exact ⟨⟨h,i'I⟩,xfi'⟩,
                rw mem_union, intro H, cases H, rw mem_bUnion at H, dsimp[I'] at H, cases H with a H', cases H' with H' H'',
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
        S = finset.bUnion T (λ t, (S.filter (λ x, f x = t))) :=
        by {ext x, split, intro xS, rw mem_bUnion,
            use f x, split, exact map x xS, rw mem_filter, split, exact xS, refl,
            rw mem_bUnion, intro A, cases A with t A, cases A with H A, rw mem_filter at A,
            exact A.1,}

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
                  have pain2 : 1 ≤ S.card := by {have tmp : S.nonempty := by {use s, exact sS,},
                                            rw ← card_pos at tmp,
                                            linarith,},
                  linarith,},
            have l_1 : disjoint S' (singleton s) := by {simp,},
            have l_2 : S = disj_union S' (singleton s)  l_1 := by {have tmp : disj_union S' (singleton s)  l_1 = S' ∪ (singleton s) :=
                                                                    by {exact disj_union_eq_union S' {s} l_1,},
                                                                    rw tmp, apply erase_union_singleton, exact sS,},
            rw l_2, rw sum_disj_union, rw sum_singleton,
            have map' : ∀ (s : α), s ∈ S' → f s ≤ r := by {intros a aS', exact map a (mem_of_mem_erase aS'),},
            specialize ih S' f sizeS' map',
            rw mul_add, rw mul_one, specialize map s sS, linarith,}

lemma sum_card_bound {α : Type*} [decidable_eq α] (r : nat)
        (S : finset α) (f : α → nat) (bound : r*S.card < ∑ s in S, (f s)) :
        ∃s,s∈S ∧ (r < f s) :=
        by {by_contra' C,
            have b1 : ∑ s in S, (f s) ≤ r*S.card :=
              by {apply sum_bound, refl, exact C,},
            linarith,}

--preimage partition is disjoint

example {α β : Type*} [decidable_eq α] [decidable_eq β] (r : nat)
        (S : finset α) (T : finset β) (f : α → β) (map : ∀(s : α), s∈S → f s ∈ T)  
        (ineq : r*T.card < S.card) : 
        ∃a, (a∈T) ∧ (r < (S.filter (λ x, f x = a)).card) :=
        by {--rw [card_disj_bUnion T S (λ t, (S.filter (λ x, f x = t))] at ineq,
            sorry,}


