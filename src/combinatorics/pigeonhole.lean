-- PIGEONHOLE PRINCIPLE (CHAPTER 27)

import data.finset.basic
import data.finset.card

import data.nat.gcd.basic
import data.nat.parity
import data.nat.prime

import tactic

open finset

variables {α β : Type*}


-- Pigeonhole principle

-- TODO: can't this be proven easier just by_contra and counting?
lemma pigeonhole
  [decidable_eq α] [decidable_eq β]
  (S : finset α) (T : finset β) (f : α → β)
  (hm : ∀ (s : α), s ∈ S → f s ∈ T )
  (hc: T.card < S.card) :
  ∃ (x ∈ S) (y ∈ S), x ≠ y ∧ f x = f y :=
begin
  -- Induction on T
  revert S, apply finset.induction_on T,

  -- Base Case when T = ∅
  { intros S hm hc, exfalso,
    by_cases S = ∅,
    { rw h at hc, exact nat.lt_irrefl _ hc, },
    { obtain ⟨s, sS⟩ := multiset.card_pos_iff_exists_mem.mp hc,
      exact hm s sS, } },

  -- Inductive Step
  { intros t T tnT IA S hm hc, -- seems to unnecessarily do a strong induction

    -- Case distinction: does t have a preimage in S
    by_cases (∃b, b ∈ S ∧ f b = t),

    -- t has a preimage in S
    { rcases h with ⟨b, bS, fbt⟩,

      -- Case distinction: does t have one or two preimages in S
      by_cases (∃b', b' ∈ S ∧ b≠ b' ∧ f b' = t),

      -- t has two distinct preimages in S
      { rcases h with ⟨b', b'S, bnb', fb't⟩,
        use [b, bS, b', b'S],
        simp [bnb', fbt, fb't], },

      -- t has only one preimage in S
      { let S' := erase S b,

        replace hm : ∀ (s : α), s ∈ S' → f s ∈ T := by {
          intros s sS',
          rw finset.mem_erase at sS',
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
        exact h, }, },

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
      exact IA S hm hc, }, }
end

-- Strong pigeonhole principle

lemma strong_pigeonhole
  [decidable_eq α] [decidable_eq β]
  (S : finset α) (T : finset β) (f : α → β)
  (hm : ∀ (s : α), s ∈ S → f s ∈ T )
  (hc: T.card < S.card) :
  ∃ (t ∈ T), T.card * (S.filter (λ s, f s = t)).card ≥ S.card :=
begin
  sorry
end

-- 1. NUMBERS

def range_from_one (n : ℕ) : finset ℕ := (list.range' 1 n).to_finset

-- Claim 1

def residue_cases (n k : ℕ) {P : Prop}
  (hs : Π (i : ℕ), (i < k) ∧ (n % k = i) → P) : P :=
begin
  sorry
end

def residue_cases_two (n : ℕ) {P : Prop}
  (h₁ : n % 2 = 0 → P) (h₂ : n % 2 = 1 → P) : P :=
begin
  have : n % 2 < 2 := nat.mod_lt n dec_trivial,
  apply lt_by_cases (n % 2) 1,
  rw nat.lt_one_iff, exact h₁,
  exact h₂, intros nP, linarith,
end

lemma neq_eq_mod
  ( n m k : ℕ ) ( h1 : n ≠ m ) ( h2 : (n+1) / k = (m+1) / k ) : 
  ∃ (r : nat), (0 < r) ∧ (r < k) ∧ (n = m + r ∨ m = n + r) :=
begin
  sorry
end

lemma neq_eq_mod_two
  ( n m : ℕ ) ( h1 : n ≠ m ) ( h2 : (n+1) / 2 = (m+1) / 2 ) : 
  n = m + 1 ∨ m = n + 1 :=
begin
  -- Lemma: (a+1) % 2 ≠ (b+1) % 2
  have Lem2 : (n+1)%2 ≠ (m+1)%2 := by {
    by_contra C, apply h1,
    linarith [nat.div_add_mod (n+1) 2, nat.div_add_mod (m+1) 2],
  },
  apply residue_cases_two (n+1),
    -- Case 1: (n + 1) % 2 == 0 → m = n + 1
    intro n_residue, apply or.inr, 
    have l1 : (m + 1) % 2 = 1 := by {
      apply residue_cases_two (m+1), intro m_residue,
      exfalso, rw m_residue at Lem2, apply Lem2, exact n_residue, simp},
    rw (add_left_inj 1).symm,
    linarith [nat.div_add_mod (n+1) 2, nat.div_add_mod (m+1) 2],
    -- Case 2: (n + 1) % 2 == 1 → n = m + 1
    intro n_residue, apply or.inl,
    have l1 : (m + 1) % 2 = 0 := by {
      apply residue_cases_two (m+1), simp, intro m_residue,
      exfalso, rw m_residue at Lem2, apply Lem2, exact n_residue},
    rw (add_left_inj 1).symm,
    linarith [nat.div_add_mod (n+1) 2, nat.div_add_mod (m+1) 2],
end

lemma succ_coprime ( n m : ℕ ) (h : n = m + 1) : nat.coprime n m :=
  by {rw h, rw nat.coprime_self_add_left, exact nat.coprime_one_left m,}

example
  (n : nat) (A: finset ℕ) (Ad : A  ⊆ range_from_one (2*n)) (Ac : A.card = (n+1)) :
  ∃ (a ∈ A) (b ∈ A), a ≠ b ∧ nat.coprime a b :=
begin
  let f := λ (x : ℕ), ((x+1) / 2),

  have h1 : ∀ (s : ℕ), s ∈ A → f s ∈ range_from_one n := by { 
    simp [range_from_one, f],
    intros s SA,
    split,
    { sorry },
    { sorry }
  },
  have h2 : (range_from_one n).card < A.card := by {
    sorry
    -- dsimp [range_from_one],
    -- rw finset.card_image_of_injective (finset.range n)
      -- (show function.injective (λ (x : ℕ), x + 1), by exact add_left_injective 1),
    -- { rw [card_range, Ac], exact nat.lt_succ_self n },
  },
    
  obtain ⟨a, aA, b, bA, anb, faefb⟩ := pigeonhole A (range_from_one n) f h1 h2,
  use [a, aA, b, bA, anb],

  cases neq_eq_mod_two a b anb faefb with h,
  { exact succ_coprime a b h },
  { exact nat.coprime.symmetric (succ_coprime b a h) }
end


-- Claim 2

lemma factor_out_prime (a : nat) (p : nat) (hp : prime p):
  ∃ (k : nat) (m : nat), a = (p^k)*m ∧ m < a ∧ ¬ (p ∣ m) :=
begin
  sorry
end

lemma factor_out_two (a : nat) :
  ∃ (k : nat) (m : nat), a = (2^k)*m ∧ m < a ∧ odd m :=
begin
  sorry
end

example
  (n : nat) (A: finset ℕ) (Ad : A  ⊆ range_from_one (2*n)) (Ac : A.card = (n+1)) :
  ∃ (a ∈ A) (b ∈ A), a ≠ b ∧ (a ∣ b) :=
begin
  sorry
end


-- 2. SEQUENCES

-- example
-- erdos szekeres
-- begin
--   sorry
-- end