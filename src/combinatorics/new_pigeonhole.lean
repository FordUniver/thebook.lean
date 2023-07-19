--Pigeonhole principle (Chapter 27)

import data.finset.basic
import data.finset.card

import data.nat.gcd.basic
import data.nat.parity

import tactic

open finset

variables {α β : Type*}

-- Pigeonhole principle

lemma pigeonhole
  [decidable_eq α] [decidable_eq β]
  (S : finset α) (T : finset β) (f : α → β)
  (hm : ∀ (s : α), s ∈ S → f s ∈ T )
  (hc: T.card < S.card) :
  ∃ (x ∈ S) (y ∈ S), x ≠ y ∧ f x = f y := by {

  -- Induction on T
  revert S,
  apply finset.induction_on T,

  -- Base Case when T = ∅
  { intros S hm hc,
    exfalso,

    -- Case distincttion: S = ∅ or S ≠ ∅
    by_cases S = ∅,
    { rw h at hc, exact nat.lt_irrefl _ hc, },
    { obtain ⟨s, sS⟩ := multiset.card_pos_iff_exists_mem.mp hc,
      exact hm s sS, } },

  -- Inductive Step
  { intros t T tnT IA S hm hc,

    -- Case distinction: does t have a preimage in S
    by_cases (∃b, b ∈ S ∧ f b = t),

    -- t has a preimage in S
    { rcases h with ⟨b, bS, fbt⟩,
      -- Case distinction: does t have one or two preimages in S
      by_cases (∃b', b' ∈ S ∧ b≠ b' ∧ f b' = t),

      -- t has two distinct preimages in S
      { rcases h with ⟨b', b'S, bnb', fb't⟩,
        use [b, bS, b', b'S],
        simp [bnb', fbt, fb't] },

      -- t has only one preimage in S
      { let S' := erase S b,

        replace hm : ∀ (s : α), s ∈ S' → f s ∈ T := by {
          intros s sS',
          rwa finset.mem_erase at sS',
          specialize hm s sS'.2, 
          rw finset.mem_insert at hm,
          cases hm,
          { exfalso,
            push_neg at h,
            specialize h s sS'.2 (ne.symm sS'.1),
            exact h hm },
          { exact hm } },

        replace hc : T.card < S'.card := by {
          rw finset.card_insert_of_not_mem tnT at hc,
          rw finset.card_erase_of_mem bS,
          have : S.card > 0 := by { exact pos_of_gt hc },
          linarith },

        specialize IA S' hm hc,
        rcases IA with ⟨x, xS, y, yS, h⟩,
        use [x, finset.mem_of_mem_erase xS, y, finset.mem_of_mem_erase yS],
        exact h,
      },
    },

    -- t does not have a preimage in S
    { replace hm: ∀ (s : α), s ∈ S → f s ∈ T := by { 
      intros s sS,
      specialize hm s sS,
      rw finset.mem_insert at hm,
      cases hm,
      { exfalso, apply h, use s, exact ⟨sS, hm⟩, }, 
      { exact hm }, },
      replace hc: T.card < S.card := by {
        rw finset.card_insert_of_not_mem tnT at hc, linarith },
      exact IA S hm hc, },
  }

}