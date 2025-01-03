/-
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Moritz Firsching, Jakob Zimmermann
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic

/-!
# Three famous lemmas on finite sets

## TODO
  - **Sperners Theorem**
    - Add the proofs of equivalences
    - Adapt variable names and proof style
  - **Erd\{o}s Ko Rado**
    - Add statement and proof
  - **Halls Theorem**
    - Add statement and proof
-/

namespace chapter30

open Function Nat Set

/-
  Definition of the basic structures
-/

structure TopDownChain (n : ℕ) where
  X : Finset (Finset (Fin n))
  chain : IsChain (· ⊆ ·) X.toSet
  top_down : Fintype.card X = n + 1

example : TopDownChain 0 := {
  X := {∅},
  chain := by
    intros x hx y hy xnegy
    simp at hx hy
    simp [hx, hy] at xnegy
  top_down := by simp
}

structure TopDownChainThrough (n : ℕ) (a : Finset (Fin n)) where
  top_down_chain : TopDownChain n
  through : a ∈ top_down_chain.X

structure TopDownChainSplitThrough (n : ℕ) (a : Finset (Fin n)) where
  bottom_chain : TopDownChain (Finset.card a)
  top_chain : TopDownChain (n - Finset.card a)

instance (n : ℕ) : DecidableEq (TopDownChain n) :=
  fun a b =>
    if h_eq : a.X = b.X then
      isTrue (by
        obtain ⟨aX, achain, atop_down⟩ := a
        obtain ⟨bX, bchain, btop_down⟩ := b
        simp
        exact h_eq)
    else
      isFalse (fun h => h_eq (congrArg (·.X) h))

instance {n : ℕ} (a : Finset (Fin n)) : DecidableEq (TopDownChainThrough n a) :=
  fun C₁ C₂ =>
    if h_eq : C₁.top_down_chain.X = C₂.top_down_chain.X then
      isTrue (by
        obtain ⟨⟨a₁, b₁, c₁⟩, through₁⟩ := C₁
        obtain ⟨⟨a₂, b₂, c₂⟩, through₂⟩ := C₂
        simp
        exact h_eq)
    else
      isFalse (fun h => h_eq (congrArg (·.top_down_chain.X) h))

instance (n : ℕ) (a : Finset (Fin n)) : DecidableEq (TopDownChainSplitThrough n a) :=
  fun C₁ C₂ =>
    if h_eq : C₁.bottom_chain.X = C₂.bottom_chain.X ∧ C₁.top_chain.X = C₂.top_chain.X then
      isTrue (by
        obtain ⟨⟨a₁₁, b₁₁, c₁₁⟩, ⟨a₁₂, b₁₂, c₁₂⟩⟩ := C₁
        obtain ⟨⟨a₂₁, b₂₁, c₂₁⟩, ⟨a₂₂, b₂₂, c₂₂⟩⟩ := C₂
        simp
        exact h_eq)
    else
      isFalse (fun h =>
        have h' : C₁.bottom_chain.X = C₂.bottom_chain.X ∧ C₁.top_chain.X = C₂.top_chain.X := by rw [h]; exact ⟨rfl, rfl⟩
        h_eq h')

/-
  Equivalence between **TopDownChain** n and **Equiv.Perm (Fin n)**
-/

def permutation_to_edge {n : ℕ} (k : Fin (n + 1)) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.image (fun (j : Fin k) => π ⟨j, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩) (Finset.univ : Finset (Fin k))

lemma permutation_to_edge_cardinality {n : ℕ} (π : Equiv.Perm (Fin n)) : ∀ k : Fin (n + 1), Finset.card (permutation_to_edge k π) = k := by
  intro k
  simp [permutation_to_edge]
  rw [Finset.card_image_of_injective]
  · simp
  · rw [Injective]
    intro a₁ a₂ h₁
    apply Fin.eq_of_val_eq
    injection (Equiv.injective π) h₁

def permutation_to_chain {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.image (fun (j : Fin (n + 1)) => permutation_to_edge j π) (Finset.univ : Finset (Fin (n + 1)))

lemma permutation_to_edge_injective {n : ℕ} {π : Equiv.Perm (Fin n)} : Injective (fun (k : Fin (n + 1)) => permutation_to_edge k π) := by
  rw [Injective]
  intro a₁ a₂ h
  have : a₁.val = a₂.val := by
    rw [←((permutation_to_edge_cardinality π) a₁), ←((permutation_to_edge_cardinality π) a₂), h]
  exact Fin.eq_of_val_eq this

def permutation_to_top_down_chain (n : ℕ) (π : Equiv.Perm (Fin n)) : TopDownChain n := {
  X := permutation_to_chain π,
  chain := by
    intros x₁ hx₁ x₂ hx₂ _
    simp [permutation_to_chain, permutation_to_edge] at hx₁ hx₂
    rcases hx₁ with ⟨k₁, hk₁⟩
    rcases hx₂ with ⟨k₂, hk₂⟩
    simp [←hk₁, ←hk₂]
    cases Nat.lt_or_ge k₁ k₂ with
    | inl k₁ltk₂ =>
        left
        intros y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨x, _, hx2⟩ := hy
        rw [←hx2]
        simp only [Finset.mem_image]
        use ⟨x.val, Nat.lt_trans x.isLt k₁ltk₂⟩
        simp
    | inr k₁gek₂ =>
        right
        intros y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨x, _, hx2⟩ := hy
        rw [←hx2]
        simp only [Finset.mem_image]
        use ⟨x.val, Nat.lt_of_lt_of_le x.isLt k₁gek₂⟩
        simp
  top_down := by
    simp
    rw [permutation_to_chain]
    rw [Finset.card_image_of_injective]
    · simp
    · exact permutation_to_edge_injective
}

/-
  A helping lemma based on the *piegon hole principle* in order to prove the existence of an edge for a given cardinality. Observe that the injectivity of edge_by_cardinality is easily verified
-/
lemma finset_exists_duplicate_image {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) (b : α) (h : ∀ a ∈ (Finset.univ : Finset α), f a ≠ b) :
  ∃ x ∈ (Finset.univ : Finset α), ∃ y ∈ (Finset.univ : Finset α), x ≠ y ∧ f x = f y := by
    let g : α → (Finset.erase (Finset.univ : Finset α) b) := fun a => ⟨f a, Finset.mem_erase.mpr ⟨h a (Finset.mem_univ a), Finset.mem_univ (f a)⟩⟩
    have imagesmaller : Fintype.card (Finset.erase (Finset.univ : Finset α) b) < Fintype.card α := by
      have : ((Finset.univ : Finset α).erase b).card < (Finset.univ : Finset α).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨b, by simp⟩) (Nat.one_pos)
      simp [this]
      exact (Finset.card_pos.mpr ⟨b, by simp⟩)
    obtain ⟨x, y, xneqy, hg⟩ := (Fintype.exists_ne_map_eq_of_card_lt g imagesmaller)
    have : f x = f y := by
      have hgx : f x = ↑(g x) := by rfl
      have hgy : f y = ↑(g y) := by rfl
      rw [hgx, hgy]
      rw [hg]
    exact ⟨x, Finset.mem_univ x, y, Finset.mem_univ y, xneqy, this⟩

/-
  In order to construct a permutation from a TopDownChain we need to have access to chain elements given their cardinality
-/
lemma edge_cardinality_upperbound {m : ℕ} (e : Finset (Fin m)): Finset.card (e) ≤ m := by
      have edge_inclusion : e ⊆ Finset.univ := Finset.subset_univ e
      have h_univ_card : m = (Finset.univ : Finset (Fin m)).card := by
        simp [Finset.card_univ]
      have := Finset.card_le_card edge_inclusion
      rw [←h_univ_card] at this
      exact this

lemma card_not_twice {n : ℕ} (C : TopDownChain n) : ∀ e₁ ∈ C.X, ∀ e₂ ∈ C.X, Finset.card e₁ = Finset.card e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ h
    by_contra hna
    cases ((C.chain he₁ he₂) hna) with
    | inl e₁sube₂ =>
      simp at e₁sube₂
      have : e₁ ⊂ e₂ := Finset.ssubset_iff_subset_ne.mpr ⟨e₁sube₂, hna⟩
      have : e₁.card < e₂.card := Finset.card_lt_card this
      linarith
    | inr e₂sube₁ =>
      simp at e₂sube₁
      have : e₂ ⊂ e₁ := Finset.ssubset_iff_subset_ne.mpr ⟨e₂sube₁, fun h => hna (Eq.symm h)⟩
      have : e₂.card < e₁.card := Finset.card_lt_card this
      linarith

def edge_by_cardinality {n : ℕ} (C : TopDownChain n) (k : Fin (n + 1)) : ∃! e ∈ C.X, Finset.card e = k := by
  have existence_edge_by_cardinality : ∃ e ∈ C.X, e.card = k := by
      by_contra ass
      simp at ass
      let list : List (Finset (Fin n)) := C.X.toList
      have list_length : list.length = n + 1 := by simp [←C.top_down, list]
      let kth_edge (j : Fin (n + 1)) : Finset (Fin n) := List.get list ⟨j.val, by rw [list_length]; exact j.isLt⟩
      have kth_edge_wd : ∀ j : Fin (n + 1), kth_edge j ∈ C.X := by
        intro j
        have : kth_edge j ∈ C.X.toList := by simp [kth_edge]
        exact Finset.mem_toList.mp this

      have edge_cardinality_range (j : Fin (n + 1)) : Finset.card (kth_edge j) < n + 1 :=
        Nat.lt_of_le_of_lt (edge_cardinality_upperbound (kth_edge j)) (Nat.lt_succ_self n)

      let kth_cardinality (j : Fin (n + 1)) : Fin (n + 1) := ⟨Finset.card (kth_edge j), edge_cardinality_range j⟩

      have h : ∀ s ∈ (Finset.univ : Finset (Fin (n + 1))), kth_cardinality s ≠ k := by
        intro s _ h₁
        simp [kth_cardinality] at h₁
        have h₂ := ass (kth_edge s) (kth_edge_wd s)
        have h₃ := congr_arg (fun (x : Fin (n + 1)) => x.val) h₁
        exact h₂ h₃

      rcases (finset_exists_duplicate_image kth_cardinality k h) with ⟨x, _, y, _, xneqy, card_equal⟩
      simp [kth_cardinality] at card_equal
      have q : list[↑x] = list[↑y] := card_not_twice C (kth_edge x) (kth_edge_wd x) (kth_edge y) (kth_edge_wd y) card_equal
      have : ↑x = ↑y := by
        let nx : Fin list.length := ⟨x.val, by rw [list_length]; exact x.isLt⟩
        let ny : Fin list.length := ⟨y.val, by rw [list_length]; exact y.isLt⟩
        by_contra ass
        have neq : nx ≠ ny := by
          intro nxeqny
          simp [nx, ny] at nxeqny
          exact ass (Fin.ext nxeqny)
        have := List.not_nodup_of_get_eq_of_ne list nx ⟨y.val, by rw [list_length]; exact y.isLt⟩ q neq
        exact this C.X.nodup_toList

      exact xneqy this

  obtain ⟨e, he⟩ := existence_edge_by_cardinality

  have uniqueness_edge_by_cardinality : ∀ (y : Finset (Fin n)), (fun u ↦ u ∈ C.X ∧ u.card = ↑k) y → y = e := by
      obtain ⟨eelt, ecard⟩ := he
      intros y hy
      obtain ⟨yelt, ycard⟩ := hy
      exact card_not_twice C y yelt e eelt (by simp [ecard, ycard])

  exact ⟨e, he, uniqueness_edge_by_cardinality⟩

instance {n : ℕ} (C : TopDownChain n) (k : Fin (n + 1)) : DecidablePred (fun (e : Finset (Fin n)) => e ∈ C.X ∧ e.card = k) := fun e => inferInstanceAs (Decidable (e ∈ C.X ∧ e.card = k))

/-
  Helper function for defining a permutation from a TopDownChain. We split the existence and uniqueness in elt_by_index into two simpler helper functions
-/

def elt_by_index_existence {n : ℕ} (C : TopDownChain n) (k : Fin n) : ∃! x ∈ (Finset.univ : Finset (Fin n)), ∀ u₁ ∈ C.X, ∀ u₂ ∈ C.X, (u₁.card = k → u₂.card = k + 1 → u₂ \ u₁ = {x}) := by
  let e₁ := (edge_by_cardinality C k).choose
  have he₁ := (edge_by_cardinality C k).choose_spec
  have e₁elt : e₁ ∈ C.X := he₁.left.left
  have e₁card : e₁.card = k := by simp [he₁.left.right]
  have e₁unique : ∀ (y : Finset (Fin n)), (fun u ↦ u ∈ C.X ∧ u.card = k) y → y = e₁ := by
    intro y hy
    have := (he₁.right y)
    simp at this
    have := this hy.1 hy.2
    simp [this, e₁]

  let e₂ := (edge_by_cardinality C (k + 1)).choose
  have he₂ := (edge_by_cardinality C (k + 1)).choose_spec
  have e₂elt : e₂ ∈ C.X := he₂.left.left
  have e₂card : e₂.card = k + 1 := by simp [he₂.left.right]
  have e₂unique : ∀ (y : Finset (Fin n)), (fun u ↦ u ∈ C.X ∧ u.card = k + 1) y → y = e₂ := by
    intro y hy
    have := (he₂.right y)
    simp at this
    have := this hy.1 hy.2
    simp [this, e₂]

  have e₁sube₂ : e₁ ⊂ e₂ := by
    have e₁nege₂ : e₁ ≠ e₂ := by
      intro ass
      have : e₁.card = k + 1 := ass.symm ▸ e₂card
      rw [e₁card] at this
      omega
    cases C.chain e₁elt e₂elt e₁nege₂ with
    | inl h =>
      exact Finset.ssubset_iff_subset_ne.mpr ⟨h, e₁nege₂⟩
    | inr h =>
      simp at h
      have := Finset.card_mono h
      rw [e₁card, e₂card] at this
      omega

  have card_difference : (e₂ \ e₁).card = 1 := by
    have := Finset.card_sdiff ((Finset.ssubset_def.mp e₁sube₂).1)
    rw [e₁card, e₂card] at this
    simp [this]

  let x := (Finset.card_eq_one.mp card_difference).choose
  let hx : e₂ \ e₁ = {x} := (Finset.card_eq_one.mp card_difference).choose_spec

  use x
  simp
  constructor
  · intro u₁ u₁elt u₂ u₂elt u₁card u₂card
    have u₁eqe₁ : u₁ = e₁ := by
      have := e₁unique u₁
      simp at this
      exact this u₁elt u₁card
    have u₂eqe₂ : u₂ = e₂ := by
      have := e₂unique u₂
      simp at this
      exact this u₂elt u₂card
    rw [u₁eqe₁, u₂eqe₂]
    exact hx
  · intros y hy
    have : e₂ \ e₁ = {y} := hy e₁ e₁elt e₂ e₂elt e₁card e₂card
    rw [hx] at this
    exact Finset.singleton_injective this.symm

def filter_fun_elt_by_index {n : ℕ} (C : TopDownChain n) (k : Fin (n + 1)) : Fin n → Prop := (fun (x : Fin n) => ∀ u₁ ∈ C.X, ∀ u₂ ∈ C.X, (u₁.card = k → u₂.card = k + 1 → u₂ \ u₁ = {x}))
instance {n : ℕ} (C : TopDownChain n) (k : Fin (n + 1)) : DecidablePred (filter_fun_elt_by_index C k) := fun x => inferInstanceAs (Decidable (∀ u₁ ∈ C.X, ∀ u₂ ∈ C.X, (u₁.card = k → u₂.card = k + 1 → u₂ \ u₁ = {x})))

lemma elt_by_index_unique {n : ℕ} (C : TopDownChain n) (k : Fin n) : ∃! a, a ∈ Finset.univ ∧ filter_fun_elt_by_index C k a := by
    simp [filter_fun_elt_by_index]
    have := elt_by_index_existence C k
    simp at this
    exact this

def elt_by_index {n : ℕ} (C : TopDownChain n) : (Fin n) → (Fin n) := fun k => Finset.choose (filter_fun_elt_by_index C k) (Finset.univ : Finset (Fin n)) (elt_by_index_unique C k)

lemma elt_by_index_injective {n : ℕ} (C : TopDownChain n) : Injective (elt_by_index C) := by
  intro x₁ x₂ fx₁x₂

  simp only [elt_by_index] at fx₁x₂

  let y₁ := Finset.choose (filter_fun_elt_by_index C x₁) Finset.univ (elt_by_index_unique C x₁)
  let hy₁ := (Finset.choose_spec (filter_fun_elt_by_index C x₁) Finset.univ (elt_by_index_unique C x₁)).right
  have hy₁_eq : y₁ = Finset.choose (filter_fun_elt_by_index C ↑↑x₁) Finset.univ (elt_by_index_unique C x₁) := rfl
  simp only [filter_fun_elt_by_index, ←hy₁_eq] at hy₁

  let y₂ := Finset.choose (filter_fun_elt_by_index C x₂) Finset.univ (elt_by_index_unique C x₂)
  let hy₂ := (Finset.choose_spec (filter_fun_elt_by_index C x₂) Finset.univ (elt_by_index_unique C x₂)).right
  have hy₂_eq : y₂ = Finset.choose (filter_fun_elt_by_index C ↑↑x₂) Finset.univ (elt_by_index_unique C x₂) := rfl
  simp only [filter_fun_elt_by_index, ←hy₂_eq] at hy₂

  have y₁eqy₂ : y₁ = y₂ := fx₁x₂

  let e₁₁ := (edge_by_cardinality C x₁).choose
  have he₁₁ := (edge_by_cardinality C x₁).choose_spec
  have e₁₁elt : e₁₁ ∈ C.X := he₁₁.left.left
  have e₁₁card : e₁₁.card = x₁ := by simp [he₁₁.left.right]

  let e₂₁ := (edge_by_cardinality C (x₁ + 1)).choose
  have he₂₁ := (edge_by_cardinality C (x₁ + 1)).choose_spec
  have e₂₁elt : e₂₁ ∈ C.X := he₂₁.left.left
  have e₂₁card : e₂₁.card = x₁ + 1 := by simp [he₂₁.left.right]

  let e₁₂ := (edge_by_cardinality C x₂).choose
  have he₁₂ := (edge_by_cardinality C x₂).choose_spec
  have e₁₂elt : e₁₂ ∈ C.X := he₁₂.left.left
  have e₁₂card : e₁₂.card = x₂ := by simp [he₁₂.left.right]

  let e₂₂ := (edge_by_cardinality C (x₂ + 1)).choose
  have he₂₂ := (edge_by_cardinality C (x₂ + 1)).choose_spec
  have e₂₂elt : e₂₂ ∈ C.X := he₂₂.left.left
  have e₂₂card : e₂₂.card = x₂ + 1 := by simp [he₂₂.left.right]

  have q₁ := hy₁ e₁₁ e₁₁elt e₂₁ e₂₁elt (by simp [e₁₁card]) (by simp [e₂₁card])
  have q₂ := hy₂ e₁₂ e₁₂elt e₂₂ e₂₂elt (by simp [e₁₂card]) (by simp [e₂₂card])

  have e₁₁nege₂₁ : e₁₁ ≠ e₂₁ := by
    intro ass
    have : e₁₁.card = e₂₁.card := by rw [ass]
    rw [e₁₁card, e₂₁card] at this
    omega

  have e₁₁sube₂₁ : e₁₁ ⊆ e₂₁ := by
    cases (C.chain e₁₁elt e₂₁elt e₁₁nege₂₁) with
    | inl h => exact h
    | inr h =>
      simp at h
      have : e₂₁.card ≤ e₁₁.card := Finset.card_mono h
      rw [e₁₁card, e₂₁card] at this
      omega

  have e₁₂nege₂₂ : e₁₂ ≠ e₂₂ := by
    intro ass
    have : e₁₂.card = e₂₂.card := by rw [ass]
    rw [e₁₂card, e₂₂card] at this
    omega

  have e₁₂sube₂₂ : e₁₂ ⊆ e₂₂ := by
    cases (C.chain e₁₂elt e₂₂elt e₁₂nege₂₂) with
    | inl h => exact h
    | inr h =>
      simp at h
      have : e₂₂.card ≤ e₁₂.card := Finset.card_mono h
      rw [e₁₂card, e₂₂card] at this
      omega

  have y₁ine₂₁ : y₁ ∈ e₂₁ := by
    apply Finset.mem_of_subset Finset.sdiff_subset
    rw [q₁]
    exact Finset.mem_singleton_self y₁

  have y₂ine₂₂ : y₂ ∈ e₂₂ := by
    apply Finset.mem_of_subset Finset.sdiff_subset
    rw [q₂]
    exact Finset.mem_singleton_self y₂

  have : e₂₁ = e₂₂ := by
    by_contra ass
    cases (C.chain e₂₁elt e₂₂elt ass) with
    | inl e₂₁sube₂₂ =>
      simp at e₂₁sube₂₂
      have e₂₁sube₁₂ : e₂₁ ⊆ e₁₂ :=
        if h : (e₂₁ = e₁₂) then (Finset.subset_of_eq h) else by
          cases (C.chain e₂₁elt e₁₂elt h) with
          | inl e₂₁sube₁₂ => exact e₂₁sube₁₂
          | inr e₁₂sube₂₁ =>
            simp at e₁₂sube₂₁
            have : e₁₂.card < e₂₁.card := Finset.card_strictMono (Finset.ssubset_iff_subset_ne.mpr ⟨e₁₂sube₂₁, (fun o => h o.symm)⟩)
            have : e₂₁.card < e₂₂.card := Finset.card_strictMono (Finset.ssubset_iff_subset_ne.mpr ⟨e₂₁sube₂₂, (fun o => ass o)⟩)
            have e₁₂union₂₂ := Finset.union_eq_right.mpr e₁₂sube₂₂
            rw [Finset.union_comm] at e₁₂union₂₂
            have := Finset.card_sdiff_add_card e₂₂ e₁₂
            rw [q₂, Finset.card_singleton, e₁₂union₂₂] at this
            linarith

      have y₂ine₁₂ : y₂ ∈ e₁₂ := by
        rw [←y₁eqy₂]
        exact Finset.mem_of_subset e₂₁sube₁₂ y₁ine₂₁
      have : y₂ ∈ e₂₂ \ e₁₂ := by
        rw [q₂]
        exact Finset.mem_singleton_self y₂

      exact False.elim ((Finset.mem_sdiff.mp this).right y₂ine₁₂)
    | inr e₂₂sube₂₁ =>
      have e₂₂sube₁₁ : e₂₂ ⊆ e₁₁ :=
        if h : (e₂₂ = e₁₁) then (Finset.subset_of_eq h) else by
          cases (C.chain e₂₂elt e₁₁elt h) with
          | inl e₂₂sube₁₁ => exact e₂₂sube₁₁
          | inr e₁₁sube₂₂ =>
            simp at e₁₁sube₂₂
            have : e₁₁.card < e₂₂.card := Finset.card_strictMono (Finset.ssubset_iff_subset_ne.mpr ⟨e₁₁sube₂₂, (fun o => h o.symm)⟩)
            have : e₂₂.card < e₂₁.card := Finset.card_strictMono (Finset.ssubset_iff_subset_ne.mpr ⟨e₂₂sube₂₁, (fun o => ass o.symm)⟩)
            have e₁₁union₂₁ := Finset.union_eq_right.mpr e₁₁sube₂₁
            rw [Finset.union_comm] at e₁₁union₂₁
            have := Finset.card_sdiff_add_card e₂₁ e₁₁
            rw [q₁, Finset.card_singleton, e₁₁union₂₁] at this
            linarith
      have y₁ine₁₁ : y₁ ∈ e₁₁ := by
        rw [y₁eqy₂]
        exact Finset.mem_of_subset e₂₂sube₁₁ y₂ine₂₂
      have : y₁ ∈ e₂₁ \ e₁₁ := by
        rw [q₁]
        exact Finset.mem_singleton_self y₁

      exact False.elim ((Finset.mem_sdiff.mp this).right y₁ine₁₁)

  have : e₂₁.card = e₂₂.card := by rw [this]
  rw [e₂₁card, e₂₂card] at this
  norm_num at this
  exact Fin.ext this

/-
  In order to use Finset.choose we need some stronger property than given by Bijective (elt_by_index C)
-/
instance {n : ℕ} (C : TopDownChain n) (y : Fin n) : DecidablePred (fun (x : Fin n) => x ∈ (Finset.univ : Finset (Fin n)) ∧ elt_by_index C x = y) := fun x => inferInstanceAs (Decidable (x ∈ (Finset.univ : Finset (Fin n)) ∧ elt_by_index C x = y))

lemma elt_by_index_surjective_constructive {n : ℕ} (C : TopDownChain n) : ∀ y : Fin n, ∃! x : Fin n, x ∈ (Finset.univ : Finset (Fin n)) ∧ elt_by_index C x = y := by
  intro y

  let e : Fin (n + 1) → Finset (Fin n) := fun x => (edge_by_cardinality C x).choose
  let I := Finset.filter (fun x => y ∈ (e x)) (Finset.univ : Finset (Fin (n + 1)))
  have image_univ : e ⟨n, by norm_num⟩ = (Finset.univ : Finset (Fin n)) := by
    let A := e ⟨n, by norm_num⟩
    have h : A = e ⟨n, by norm_num⟩ := rfl
    rw [←h]
    simp [e] at h
    have := ((edge_by_cardinality C n).choose_spec).left
    simp [←h] at this

    apply Finset.eq_univ_of_card A
    rw [←Finset.card_univ, Finset.card_fin n]
    exact this.right

  have image_empty : e ⟨0, by norm_num⟩ = ∅ := by
    let A := e ⟨0, by norm_num⟩
    have h : A = e ⟨0, by norm_num⟩ := rfl
    rw [←h]
    simp [e] at h
    have := ((edge_by_cardinality C 0).choose_spec).left
    simp [←h] at this
    exact this.right

  have ninI : ⟨n, by norm_num⟩ ∈ I := by
    simp [I]
    rw [image_univ]
    exact Finset.mem_univ y

  have h : I.Nonempty := ⟨⟨n, by norm_num⟩, ninI⟩

  let x := (Finset.min_of_nonempty h).choose
  let hx : I.min = x := (Finset.min_of_nonempty h).choose_spec

  have : ∀ z : Fin (n + 1), z < x → y ∉ (e z) := by
    intro z zlty
    have : z < I.min := by simp [hx]; exact zlty
    have : z ∉ I := Finset.not_mem_of_coe_lt_min this
    contrapose this
    simp
    simp at this
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ z
    · exact this

  have zeroltx : 0 < x := by
    by_contra ass
    have xzero : x = 0 := by
      have : ¬0 < x.val := fun h => ass (Fin.lt_def.mpr h)
      have : x.val = 0 := Nat.eq_zero_of_not_pos this
      exact Fin.ext this
    have : 0 ∈ I := by rw [←xzero]; exact Finset.mem_of_min hx
    have := (Finset.mem_filter.mp this).right
    rw [image_empty] at this
    simp at this

  have xminusoneltn : x.val - 1 < n := by
    have : x.val < n + 1 := x.isLt
    simp [Nat.add_comm n 1] at this
    exact Nat.sub_lt_left_of_lt_add (by norm_cast) this

  let w : Fin n := ⟨x - 1, xminusoneltn⟩
  use w

  simp

  have hw : elt_by_index C w = y := by
    have hy₁ : y ∉ e w := by
      have wltx : w < x := by
        simp [w]
        apply Fin.lt_def.mpr
        norm_num
        have : (↑x - 1) % (n + 1) = (↑x - 1) := by
          apply Nat.mod_eq_of_lt
          have : ↑x < n + 1 := x.isLt
          linarith
        rw [this]
        norm_num
        exact zeroltx
      exact this w wltx

    have hy₂ : y ∈ e (w + 1) := by
      have xw : x = ↑↑w + 1 := by
        simp [w]
        norm_cast
        rw [Nat.sub_add_cancel]
        simp
        norm_cast

      have : x ∈ I := Finset.mem_of_min hx
      simp [I] at this
      rw [xw] at this
      exact this

    have hy : y ∈ e (w + 1) \ e w := by simp [hy₁, hy₂]

    let u := elt_by_index C w

    let hu : filter_fun_elt_by_index C w u:= (Finset.choose_spec (filter_fun_elt_by_index C w) (Finset.univ : Finset (Fin n)) (elt_by_index_unique C w)).right
    simp [filter_fun_elt_by_index] at hu

    let e₁ := e w
    have he₁ := (edge_by_cardinality C w).choose_spec
    have e₁elt : e₁ ∈ C.X := he₁.left.left
    have e₁card : e₁.card = (↑x - 1) % (n + 1) := by simp [he₁.left.right]

    let e₂ := e (w + 1)
    have he₂ := (edge_by_cardinality C (w + 1)).choose_spec
    have e₂elt : e₂ ∈ C.X := he₂.left.left
    have e₂card : e₂.card = (↑x - 1) % (n + 1) + 1 := by
      simp [he₂.left.right]
      norm_cast
      rw [Nat.sub_add_cancel]
      simp
      apply (Nat.sub_eq_iff_eq_add (by norm_cast)).mp
      apply Eq.symm
      apply (Nat.mod_eq_iff_lt (by norm_cast)).mpr
      linarith
      norm_cast

    have usingleton : e₂ \ e₁ = {u} := hu e₁ e₁elt e₂ e₂elt e₁card e₂card

    have e₁nege₂ : e₁ ≠ e₂ := by
      intro ass
      have : e₁.card = e₂.card := by rw [ass]
      rw [e₁card, e₂card] at this
      omega

    have e₁sube₂ : e₁ ⊆ e₂ := by
      cases (C.chain e₁elt e₂elt e₁nege₂) with
      | inl h => exact h
      | inr h =>
        simp at h
        have : e₂.card ≤ e₁.card := Finset.card_mono h
        rw [e₁card, e₂card] at this
        omega

    have : e₂ \ e₁ = {y} := by
      have diff_card : (e₂ \ e₁).card = 1 := by
        calc
          (e₂ \ e₁).card = e₂.card - e₁.card := Finset.card_sdiff e₁sube₂
          _ = (↑x - 1) % (n + 1) + 1 - (↑x - 1) % (n + 1) := by rw [e₁card, e₂card]
          _ = 1 := by norm_num

      obtain ⟨y_, hy_⟩ := Finset.card_eq_one.mp diff_card
      simp [hy_]
      apply Eq.symm
      apply Finset.mem_singleton.mp
      rw [←hy_]
      exact hy

    rw [usingleton] at this
    exact Finset.singleton_injective this

  constructor
  · exact hw
  · intro x₂ hwx₂
    rw [←hw] at hwx₂
    exact (elt_by_index_injective C) hwx₂

def elt_by_index_inverse {n : ℕ} (C : TopDownChain n) : Fin n → Fin n := fun y => Finset.choose (fun (x : Fin n) => elt_by_index C x = y) (Finset.univ : Finset (Fin n)) (elt_by_index_surjective_constructive C y)

def top_down_chain_to_permutation (n : ℕ) (C : TopDownChain n) : Equiv.Perm (Fin n) := {
  toFun := elt_by_index C

  invFun := elt_by_index_inverse C

  left_inv := by
    intro x
    let y := elt_by_index C x
    have hy : y = elt_by_index C x := rfl
    simp [elt_by_index_inverse, ←hy]
    have unique_existence := (elt_by_index_surjective_constructive C y)
    obtain ⟨_, exprop⟩ := Finset.choose_spec (fun (x : Fin n) => elt_by_index C x = y) (Finset.univ : Finset (Fin n)) unique_existence

    apply ExistsUnique.unique unique_existence

    · constructor
      · simp
      · exact exprop
    · constructor
      · simp
      · exact hy

  right_inv := by
    intro y
    let x := elt_by_index_inverse C y
    have hx : x = elt_by_index_inverse C y := rfl
    simp only [←hx]

    simp only [elt_by_index_inverse] at hx

    have unique_existence := elt_by_index_surjective_constructive C y
    have ⟨_, exprop⟩ := Finset.choose_spec (fun (x : Fin n) => elt_by_index C x = y) (Finset.univ : Finset (Fin n)) unique_existence
    simp only [←hx] at exprop

    exact exprop
}


theorem top_down_chain_to_permutation_bijective (n : ℕ) : (Bijective (top_down_chain_to_permutation n)) := by sorry

theorem permutation_to_top_down_chain_bijective (n : ℕ) : (Bijective (permutation_to_top_down_chain n)) := by sorry

instance (n : ℕ) : Fintype (TopDownChain n) := {
  elems := Finset.image (fun π => permutation_to_top_down_chain n π) (Finset.univ : Finset (Equiv.Perm (Fin n)))
  complete := by
    intro C
    simp
    exact (permutation_to_top_down_chain_bijective n).right C
}

/-
  Equivalence between **TopDownChainThrough n a** and **TopDownChainSplitThrough n a**
-/

def TopDownChainSplitThrough_embedding (n : ℕ) (a : Finset (Fin n)) : ((TopDownChain a.card) × (TopDownChain (n - a.card))) → TopDownChainSplitThrough n a :=
  fun (bottom, top) => (⟨bottom, top⟩ : TopDownChainSplitThrough n a)

instance (n : ℕ) (a : Finset (Fin n)) : Fintype (TopDownChainSplitThrough n a) := {
  elems := Finset.image (TopDownChainSplitThrough_embedding n a) (Finset.univ : Finset ((TopDownChain a.card) × (TopDownChain (n - a.card)))),
  complete := by
    intro C
    simp [TopDownChainSplitThrough_embedding]
}

lemma TopDownChainSplitThrough_embedding_bijective (n : ℕ) (a : Finset (Fin n)) : Bijective (TopDownChainSplitThrough_embedding n a) := by
  constructor
  · intro ⟨bottom₁, top₁⟩ ⟨bottom₂, top₂⟩ ass
    simp [TopDownChainSplitThrough_embedding] at ass
    simp [ass]
  · intro ⟨bottom, top⟩
    use (bottom, top)
    simp [TopDownChainSplitThrough_embedding]

def translate_edge {n m : ℕ} (list : List (Fin n)) (list_length : list.length = m) : Finset (Fin m) → Finset (Fin n) := fun e => (Finset.image (fun j : Fin m => (list.get ⟨j.val, by rw [list_length]; exact j.isLt⟩)) e)

lemma translate_edge_injective (n m : ℕ) (list : List (Fin n)) (list_length : list.length = m) (nodups : list.Nodup): Injective (translate_edge list list_length) := by
  intro e₁ e₂ he₁e₂
  ext x
  constructor
  · intro xine₁
    have x_in_filter₁ : list.get ⟨x, by simp [list_length]⟩ ∈ translate_edge list list_length e₂ := by
      rw [←he₁e₂]
      simp [translate_edge]
      exact ⟨x, ⟨xine₁, rfl⟩⟩
    simp [translate_edge] at x_in_filter₁
    obtain ⟨j, ⟨jine₂, hj⟩⟩ := x_in_filter₁
    have get_injective : Function.Injective list.get := List.nodup_iff_injective_get.mp nodups
    have := Fin.ext_iff.mp (get_injective hj)
    simp at this
    have := Fin.ext this
    rw [this] at jine₂
    exact jine₂
  · intro xine₁
    have x_in_filter₂ : list.get ⟨x, by simp [list_length]⟩ ∈ translate_edge list list_length e₁ := by
      rw [he₁e₂]
      simp [translate_edge]
      exact ⟨x, ⟨xine₁, rfl⟩⟩
    simp [translate_edge] at x_in_filter₂
    obtain ⟨j, ⟨jine₁, hj⟩⟩ := x_in_filter₂
    have get_injective : Function.Injective list.get := List.nodup_iff_injective_get.mp nodups
    have := Fin.ext_iff.mp (get_injective hj)
    simp at this
    have := Fin.ext this
    rw [this] at jine₁
    exact jine₁

def translate_bottom_chain {n m : ℕ} (X : Finset (Finset (Fin m))) (list : List (Fin n)) (list_length : list.length = m) : Finset (Finset (Fin n)) := Finset.image (translate_edge list list_length) X

lemma chain_translate_chain {n m : ℕ} (X : Finset (Finset (Fin m))) (list : List (Fin n)) (list_length : list.length = m) (chain : IsChain (· ⊆ ·) X.toSet)
  (e₁ : Finset (Fin n)) (e₁elt : ∃ x ∈ X, translate_edge list list_length x = e₁) (e₂ : Finset (Fin n)) (e₂elt : ∃ x ∈ X, translate_edge list list_length x = e₂) (e₁nee₂ : e₁ ≠ e₂) : e₁ ⊆ e₂ ∨ e₂ ⊆ e₁ := by

    obtain ⟨u₁, ⟨u₁elt, u₁image⟩⟩ := e₁elt
    obtain ⟨u₂, ⟨u₂elt, u₂image⟩⟩ := e₂elt

    have u₁neu₂ : u₁ ≠ u₂ := by
      intro ass
      have :=
        calc
          e₁ = translate_edge list list_length u₁ := u₁image.symm
          _ = translate_edge list list_length u₂ := by rw [ass]
          _ = e₂ := u₂image
      exact e₁nee₂ this

    cases chain u₁elt u₂elt u₁neu₂ with
    | inl u₁subu₂ =>
      left
      intro x xine₁
      simp [←u₁image, translate_edge] at xine₁
      obtain ⟨j₁, ⟨j₁inu₁, hj₁⟩⟩ := xine₁
      have j₁inu₂ := u₁subu₂ j₁inu₁
      simp [←u₂image, translate_edge]
      exact ⟨j₁, ⟨j₁inu₂, hj₁⟩⟩
    | inr u₂subu₁ =>
      right
      intro x xine₂
      simp [←u₂image, translate_edge] at xine₂
      obtain ⟨j₂, ⟨j₂inu₂, hj₂⟩⟩ := xine₂
      have j₂inu₁ := u₂subu₁ j₂inu₂
      simp [←u₁image, translate_edge]
      exact ⟨j₂, ⟨j₂inu₁, hj₂⟩⟩

noncomputable def split_to_TopDownChainThrough (n : ℕ) (a : Finset (Fin n)) : TopDownChainSplitThrough n a → TopDownChainThrough n a := by
  intro C

  let top_elements := (Finset.univ : Finset (Fin n)) \ a

  have top_elements_card : top_elements.card = n - a.card := by
    have h_univ : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
    have : top_elements.card + a.card = Finset.univ.card := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ a)
    rw [h_univ] at this
    exact (Nat.sub_eq_of_eq_add this.symm).symm

  have disjoint_helper (e : Finset (Fin (n - a.card))) : Disjoint ((translate_edge top_elements.toList (by simp [top_elements_card])) e) a := by
    intro u usub usuba
    simp [translate_edge] at usub
    intro x xinu
    have := usub xinu
    simp at this
    obtain ⟨j, ⟨_, hj⟩⟩ := this

    have : x ∈ top_elements.toList := by
      rw [←hj]
      apply List.getElem_mem

    have xintop : x ∈ top_elements := Finset.mem_toList.mp this
    simp [top_elements] at xintop
    exact False.elim (xintop (usuba xinu))

  let bottom_chain_embedding := Finset.image (translate_edge a.toList (by simp)) C.bottom_chain.X
  let top_translate_edge : Finset (Fin (n - a.card)) → Finset (Fin n) := fun e => Finset.disjUnion ((translate_edge top_elements.toList (by simp [top_elements_card])) e) a (disjoint_helper e)
  let top_chain_embedding := Finset.image top_translate_edge (C.top_chain.X \ {∅})

  have embeddings_disjoint : Disjoint bottom_chain_embedding top_chain_embedding := by
    intro E Ebottom Etop
    simp
    intro e einE

    have einbottom := Ebottom einE
    simp [bottom_chain_embedding] at einbottom
    obtain ⟨_, ⟨_, hebottom⟩⟩ := einbottom

    have eintop := Etop einE
    simp [top_chain_embedding] at eintop
    obtain ⟨w, ⟨welt, hetop⟩⟩ := eintop

    have : 1 + a.card ≤ e.card := by
      simp [top_translate_edge] at hetop
      have : e = Finset.disjUnion ((translate_edge top_elements.toList (by simp [top_elements_card])) w) a (disjoint_helper w) := by simp [hetop]
      rw [this, Finset.card_disjUnion]
      simp
      apply Finset.image_nonempty.mpr
      exact Finset.nonempty_iff_ne_empty.mpr welt.right

    have : e.card ≤ a.card := by
      simp [←hebottom]
      apply Finset.card_mono
      intro y yelt
      simp [translate_edge] at yelt
      obtain ⟨_, ⟨_, h⟩⟩ := yelt
      apply Finset.mem_toList.mp
      rw [←h]
      apply List.getElem_mem

    linarith

  let top_down_chain : TopDownChain n := {
    X := Finset.disjUnion bottom_chain_embedding top_chain_embedding embeddings_disjoint
    chain := by
      intro e₁ e₁elt e₂ e₂elt e₁nee₂
      cases Finset.mem_disjUnion.mp e₁elt with
      | inl e₁inbottom =>
        simp [bottom_chain_embedding] at e₁inbottom
        cases Finset.mem_disjUnion.mp e₂elt with
        | inl e₂inbottom =>
          simp [bottom_chain_embedding] at e₂inbottom
          exact chain_translate_chain C.bottom_chain.X a.toList (by simp) C.bottom_chain.chain e₁ e₁inbottom e₂ e₂inbottom e₁nee₂
        | inr e₂intop =>
          left
          simp [top_chain_embedding] at e₂intop
          obtain ⟨preimagee₂, ⟨_, h₃⟩⟩ := e₂intop
          have : e₁ ⊆ a := by
            obtain ⟨preimagee₁, ⟨_, he₁⟩⟩ := e₁inbottom
            rw [←he₁]
            intro x xelt
            simp [translate_edge] at xelt
            obtain ⟨j, ⟨_, hj⟩⟩ := xelt
            rw [←hj]
            apply Finset.mem_toList.mp
            apply List.getElem_mem
          rw [←h₃]
          intro x xine₁
          simp [top_translate_edge]
          right
          exact this xine₁
      | inr e₁intop =>
        simp [top_chain_embedding] at e₁intop
        cases Finset.mem_disjUnion.mp e₂elt with
        | inr e₂intop =>
          simp [top_chain_embedding] at e₂intop
          obtain ⟨preimagee₁, ⟨preimagee₁elt, _⟩, hpreimagee₁⟩ := e₁intop
          obtain ⟨preimagee₂, ⟨preimagee₂elt, _⟩, hpreimagee₂⟩ := e₂intop
          let u₁ := e₁ \ a
          let u₂ := e₂ \ a
          have u₁neu₂ : u₁ ≠ u₂ := by
            intro ass
            have : (e₁ \ a) ∪ a = (e₂ \ a) ∪ a := by
              have hu₁ : e₁ \ a = u₁ := rfl
              have hu₂ : e₂ \ a = u₂ := rfl
              rw [hu₁, hu₂, ass]
            have h₁ : e₁ \ a ∪ a = e₁ := by
              rw [←hpreimagee₁]
              simp [top_translate_edge]
            have h₂ : e₂ \ a ∪ a = e₂ := by
              rw [←hpreimagee₂]
              simp [top_translate_edge]
            rw [h₁, h₂] at this
            exact e₁nee₂ this

          have hu₁ : u₁ = translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₁ := by
            let u := translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₁
            have hu : u = translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₁ := rfl
            simp [u₁, ←hpreimagee₁, ←hu, top_translate_edge]
            apply Finset.union_sdiff_cancel_right

            exact disjoint_helper preimagee₁

          have hu₂ : u₂ = translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₂ := by
            let u := translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₂
            have hu : u = translate_edge top_elements.toList (by simp [top_elements_card]) preimagee₂ := rfl
            simp [u₂, ←hpreimagee₂, ←hu, top_translate_edge]
            apply Finset.union_sdiff_cancel_right

            exact disjoint_helper preimagee₂


          have := chain_translate_chain C.top_chain.X top_elements.toList (by simp [top_elements_card]) C.top_chain.chain u₁ ⟨preimagee₁, ⟨preimagee₁elt, hu₁.symm⟩⟩ u₂ ⟨preimagee₂, ⟨preimagee₂elt, hu₂.symm⟩⟩ u₁neu₂
          simp [top_translate_edge, ←hu₁] at hpreimagee₁
          simp [top_translate_edge, ←hu₂] at hpreimagee₂

          have disjoint₁ := disjoint_helper preimagee₁
          rw [←hu₁] at disjoint₁
          have u₁indisjoint : e₁ = Finset.disjUnion u₁ a disjoint₁ := by simp [hpreimagee₁]

          have disjoint₂ := disjoint_helper preimagee₂
          rw [←hu₂] at disjoint₂
          have u₂indisjoint : e₂ = Finset.disjUnion u₂ a disjoint₂ := by simp [hpreimagee₂]

          cases this with
          | inl u₁inu₂ =>
            left
            intro x xine₁

            rw [u₁indisjoint] at xine₁
            rw [u₂indisjoint]

            cases Finset.mem_disjUnion.mp xine₁ with
            | inl h =>
              apply Finset.mem_disjUnion.mpr
              left
              exact u₁inu₂ h

            | inr h =>
              apply Finset.mem_disjUnion.mpr
              right
              exact h
          | inr u₂inu₁ =>
            right
            intro x xine₂

            rw [u₂indisjoint] at xine₂
            rw [u₁indisjoint]

            cases Finset.mem_disjUnion.mp xine₂ with
            | inl h =>
              apply Finset.mem_disjUnion.mpr
              left
              exact u₂inu₁ h

            | inr h =>
              apply Finset.mem_disjUnion.mpr
              right
              exact h

        | inl e₂inbottom =>
          right
          simp [bottom_chain_embedding] at e₂inbottom
          obtain ⟨preimagee₁, ⟨_, h₃⟩⟩ := e₁intop

          have : e₂ ⊆ a := by
            obtain ⟨preimagee₂, ⟨_, he₂⟩⟩ := e₂inbottom
            rw [←he₂]
            intro x xelt
            simp [translate_edge] at xelt
            obtain ⟨j, ⟨_, hj⟩⟩ := xelt
            rw [←hj]
            apply Finset.mem_toList.mp
            apply List.getElem_mem

          rw [←h₃]
          intro x xine₂
          simp [top_translate_edge]
          right
          exact this xine₂

    top_down := by
      have : Fintype.card { x // x ∈ bottom_chain_embedding.disjUnion top_chain_embedding embeddings_disjoint }
              = Finset.card (bottom_chain_embedding.disjUnion top_chain_embedding embeddings_disjoint) := Fintype.card_ofFinset _ (fun x => Iff.rfl)
      rw [this, Finset.card_disjUnion]
      simp [bottom_chain_embedding, top_chain_embedding]
      rw [Finset.card_image_of_injective C.bottom_chain.X (translate_edge_injective n a.card a.toList (by simp) a.nodup_toList)]
      have top_translate_edge_injective : Injective top_translate_edge := by
        intro e₁ e₂ he₁e₂
        simp only [top_translate_edge] at he₁e₂

        let specific_translate_edge : Finset (Fin (n - a.card)) → Finset (Fin n) := translate_edge top_elements.toList (by simp [top_elements_card])
        have h : (specific_translate_edge : Finset (Fin (n - a.card)) → Finset (Fin n)) = translate_edge top_elements.toList (by simp [top_elements_card]) := rfl

        simp [←h] at he₁e₂

        have : specific_translate_edge e₁ = specific_translate_edge e₂ := by
          ext z
          constructor
          · intro zelt
            have : z ∈ (specific_translate_edge e₁) ∪ a := by simp [zelt]
            simp [he₁e₂] at this
            cases this with
            | inl zin => exact zin
            | inr zina =>
                have := disjoint_helper e₁
                rw [←h] at this
                have := (Finset.disjoint_iff_ne.mp this) z zelt z zina
                simp at this
          · intro zelt
            have : z ∈ (specific_translate_edge e₂) ∪ a := by simp [zelt]
            simp [←he₁e₂] at this
            cases this with
            | inl zin => exact zin
            | inr zina =>
                have := disjoint_helper e₂
                rw [←h] at this
                have := (Finset.disjoint_iff_ne.mp this) z zelt z zina
                simp at this

        have injectivity : Injective specific_translate_edge := (translate_edge_injective n (n - a.card) top_elements.toList (by simp [top_elements_card]) top_elements.nodup_toList)

        exact injectivity this


      rw [Finset.card_image_of_injective (C.top_chain.X \ {∅}) top_translate_edge_injective]
      have fst_term : Fintype.card C.bottom_chain.X = C.bottom_chain.X.card := Fintype.card_ofFinset _ (fun x => Iff.rfl)
      have get_rid_of_empty : (C.top_chain.X \ {∅}).card = C.top_chain.X.card - 1 := by
        apply Eq.symm
        apply Nat.sub_eq_of_eq_add
        apply Eq.symm
        rw [←(Finset.card_singleton (∅ : Finset (Fin n)))]
        apply Finset.card_sdiff_add_card_eq_card
        simp
        obtain ⟨⟨e, ecard⟩, _⟩ := (edge_by_cardinality C.top_chain ⟨0, by norm_num⟩).choose_spec
        simp at ecard
        simp [ecard] at e
        exact e
      have snd_term : Fintype.card C.top_chain.X = C.top_chain.X.card := Fintype.card_ofFinset _ (fun x => Iff.rfl)
      rw [←fst_term, C.bottom_chain.top_down, get_rid_of_empty, ←snd_term, C.top_chain.top_down]
      rw [Nat.add_sub_cancel, Nat.add_assoc, Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel, Nat.add_comm]

      · simp_rw [←(Finset.card_fin n)]
        apply Finset.card_mono
        simp

  }

  let result : TopDownChainThrough n a := {
    top_down_chain := top_down_chain
    through := by
      simp [bottom_chain_embedding]
      left
      let preimage := (edge_by_cardinality C.bottom_chain a.card).choose
      have : preimage ∈ C.bottom_chain.X ∧ preimage.card = a.card := by simp [(edge_by_cardinality C.bottom_chain a.card).choose_spec.left]
      use preimage
      constructor
      · exact this.left
      · apply Finset.eq_of_subset_of_card_le
        · simp [translate_edge]
          intro x xin
          simp at xin
          obtain ⟨j, ⟨_, hj⟩⟩ := xin

          apply Finset.mem_toList.mp
          rw [←hj]
          apply List.getElem_mem
        · apply Nat.le_of_eq

          simp [translate_edge]
          have injectivity_get : Injective (fun j : Fin a.card => (a.toList[j.val])) := by
            intro a₁ a₂ ha₁a₂
            have := Fin.ext_iff.mp ((List.nodup_iff_injective_get.mp a.nodup_toList) ha₁a₂)
            exact Fin.ext this

          simp_rw [Finset.card_image_of_injective (preimage) injectivity_get]
          exact this.right.symm
  }

  exact result

theorem split_to_TopDownChainThrough_bijective (n : ℕ) (a : Finset (Fin n)) : Bijective (split_to_TopDownChainThrough n a) := by sorry


noncomputable instance (n : ℕ) (a : Finset (Fin n)) : Fintype (TopDownChainThrough n a) := {
  elems := Finset.image (fun π => split_to_TopDownChainThrough n a π) (Finset.univ : Finset (TopDownChainSplitThrough n a))
  complete := by
    intro C
    simp
    exact (split_to_TopDownChainThrough_bijective n a).right C
}

/-
  Lemmata about cardinalities
-/

lemma cardinality_ChainThrough {n : ℕ} (a : Finset (Fin n)) :
  (Finset.univ : Finset (TopDownChainThrough n a)).card = (Finset.univ : Finset (TopDownChainSplitThrough n a)).card := by
    apply Eq.symm
    apply Finset.card_eq_of_equiv
    have := Equiv.ofBijective (split_to_TopDownChainThrough n a) (split_to_TopDownChainThrough_bijective n a)
    have tdc_through_equiv := Equiv.Set.univ (TopDownChainThrough n a)
    have tdc_split_equiv := Equiv.Set.univ (TopDownChainSplitThrough n a)
    simp

    exact (tdc_split_equiv.trans this).trans tdc_through_equiv.symm

lemma cardinality_TopDownChain (n : ℕ) : (Finset.univ : Finset (TopDownChain n)).card = (n)! := by
    calc
      (Finset.univ : Finset (TopDownChain n)).card = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
        apply Finset.card_bijective (top_down_chain_to_permutation n) (top_down_chain_to_permutation_bijective n) (fun i => ⟨fun _ => by simp, fun _ => by simp⟩)
      _ = Fintype.card (Equiv.Perm (Fin n)) := by simp
      _ = (Fintype.card (Fin n))! := Fintype.card_perm
      _ = (n)! := by rw [Fintype.card_fin n]

lemma cardinality_ChainSplitThrough {n : ℕ} (a : Finset (Fin n)) :
  (Finset.univ : Finset (TopDownChainSplitThrough n a)).card = (a.card)! * (n - a.card)! := by
    have hst : ∀ i, i ∈ (Finset.univ : Finset ((TopDownChain a.card) × (TopDownChain (n - a.card)))) ↔ (TopDownChainSplitThrough_embedding n a) i ∈ (Finset.univ : Finset (TopDownChainSplitThrough n a)) := by
      intro i
      constructor <;> simp
    rw [←Finset.card_bijective (TopDownChainSplitThrough_embedding n a) (TopDownChainSplitThrough_embedding_bijective n a) hst]
    rw [Finset.card_univ]
    rw  [Fintype.card_prod]
    have fst_eq : Fintype.card (TopDownChain a.card) = a.card ! := by rw [←(cardinality_TopDownChain a.card)]; simp
    have snd_eq: Fintype.card (TopDownChain (n - a.card)) = (n - a.card)! := by rw [←(cardinality_TopDownChain (n - a.card))]; simp
    rw [fst_eq, snd_eq]

/-
  **Sperners Theorem**
-/

theorem Sperner {n : ℕ} {A : Finset (Finset (Fin n))} :
  (∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ → ¬(e₁ ⊆ e₂)) → A.card ≤ n.choose (n / 2) := by
    intro h_antichain

    let M : Fin (n + 1) → Finset (Finset (Fin n)) := fun k => { e | e ∈ A ∧ Finset.card e = k }
    let m : Fin (n + 1) → ℕ := fun k => Finset.card (M k)

    have pairwisedisjointM : (Set.univ : Set (Fin (n + 1))).PairwiseDisjoint M := by
      intro i hi j hj inegj
      intro a hai haj b bina
      simp [M] at *
      have bcardi : b.card = i := by
        have := hai bina
        simp at this
        exact this.2
      have bcardj : b.card = j := by
        have := haj bina
        simp at this
        exact this.2
      have : i.val = j.val := by rw [←bcardi, ←bcardj]
      exact inegj (Fin.ext this)

    have disjointcardinalityunion : A = (Finset.univ : Finset (Fin (n + 1))).disjiUnion M (by simp [pairwisedisjointM]) := by
      ext e
      constructor
      · intro he
        apply Finset.mem_disjiUnion.mpr
        use ⟨Finset.card e, Nat.lt_succ.mpr (edge_cardinality_upperbound e)⟩
        simp [M, he]
      · intro he
        simp [Finset.biUnion, M] at he
        exact he.1

    have cardassum : A.card = ∑ (k : Fin (n + 1)), m k := by
      rw [disjointcardinalityunion, Finset.card_disjiUnion (Finset.univ : Finset (Fin (n + 1))) M (by simp [pairwisedisjointM])]

    have disjoint_top_down_chains: ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁ ≠ e₂ → ∀ C₁ : TopDownChainThrough n e₁, ∀ C₂ : TopDownChainThrough n e₂, C₁.top_down_chain.X ≠ C₂.top_down_chain.X := by
      intro e₁ he₁ e₂ he₂ e₁nege₂ C₁ C₂
      by_contra ass
      have e₁inC₂ : e₁ ∈ C₂.top_down_chain.X := by
        rw [←ass]
        exact C₁.through
      cases (C₂.top_down_chain.chain e₁inC₂ C₂.through e₁nege₂ : e₁ ⊆ e₂ ∨ e₂ ⊆ e₁) with
      | inl e₁ine₂ => exact h_antichain e₁ he₁ e₂ he₂ e₁nege₂ e₁ine₂
      | inr e₂ine₁ => exact h_antichain e₂ he₂ e₁ he₁ (by by_contra q; exact e₁nege₂ (Eq.symm q)) e₂ine₁

    let f_embedded_chains (e : Finset (Fin n)) : (TopDownChainThrough n e) → (TopDownChain n) := fun C => C.top_down_chain

    let embedded_chains : Finset (Fin n) → Finset (TopDownChain n) := fun e => ((Finset.univ : Finset (TopDownChainThrough n e)).image (f_embedded_chains e))

    have embedded_chains_cardinality (e : Finset (Fin n)) : (embedded_chains e).card = (Finset.univ : Finset (TopDownChainThrough n e)).card := by
      simp [embedded_chains]
      apply Finset.card_image_of_injective
      · intro e₁ e₂ he₁e₂
        simp [f_embedded_chains] at he₁e₂
        cases e₁
        cases e₂
        simp at he₁e₂
        simp [he₁e₂]

    have hf : Set.PairwiseDisjoint A embedded_chains := by
      intros e₁ e₁elt e₂ e₂elt e₁nee₂
      intros u usub₁ usub₂
      intro x xinu
      have xelt₁ := usub₁ xinu
      simp [embedded_chains] at xelt₁
      have xelt₂ := usub₂ xinu
      simp [embedded_chains] at xelt₂
      obtain ⟨C₁, hC₁⟩ := xelt₁
      obtain ⟨C₂, hC₂⟩ := xelt₂

      simp [f_embedded_chains] at hC₁
      simp [f_embedded_chains] at hC₂

      have := disjoint_top_down_chains e₁ e₁elt e₂ e₂elt e₁nee₂ C₁ C₂
      rw [←hC₂] at hC₁
      have h : C₁.top_down_chain.X = C₂.top_down_chain.X := by rw [hC₁]
      exact False.elim (this h)

    let chains_through_A := A.disjiUnion embedded_chains hf

    have central_inequality : ∑ k : Fin (n + 1), (m k) * (k)! * (n - k)! ≤ (n)! := by
      calc
        ∑ k : Fin (n + 1), (m k) * (k)! * (n - k)! = ∑ k : Fin (n + 1), ∑ e ∈ (M k), (e.card)! * (n - e.card)! := by
          apply Finset.sum_congr
          simp
          intro k _
          have hq : ∀ e ∈ M k, (e.card)! * (n - e.card)! = (k)! * (n - k)! := by
            intro e he
            simp [M] at he
            rw [he.2]
          rw [Finset.sum_congr rfl (fun x q => hq x q)]
          simp [m]
          ring
        _ = ∑ e ∈ A, (e.card)! * (n - e.card)! := by
          rw [disjointcardinalityunion]
          exact (Finset.univ.sum_disjiUnion M (by simp [pairwisedisjointM])).symm
        _ = ∑ e ∈ A, (Finset.univ : Finset (TopDownChainSplitThrough n e)).card := by
          apply Finset.sum_congr
          simp
          intro e _
          exact Eq.symm (cardinality_ChainSplitThrough e)
        _ = ∑ e ∈ A, (embedded_chains e).card := by
          apply Finset.sum_congr
          simp
          intro e _
          rw [embedded_chains_cardinality, cardinality_ChainThrough e]
        _ = chains_through_A.card := (Finset.card_disjiUnion A embedded_chains hf).symm
        _ ≤ (Finset.univ : Finset (TopDownChain n)).card := by
          have : chains_through_A ⊆ (Finset.univ : Finset (TopDownChain n)) := by simp
          exact Finset.card_mono this
        _ = (n)! := cardinality_TopDownChain n

    have div_helper (a b c : ℚ) : 1 / (a / (b * c)) = b * c * (1 / a) := by rw [←div_eq_mul_one_div (b * c) a]; simp

    have : A.card / (n.choose (n / 2) : ℚ) ≤ 1 := by
      calc
        A.card / ↑(n.choose (n / 2)) = (∑ (k : Fin (n + 1)), ↑(m k)) * (1 / (n.choose (n / 2) : ℚ)) := by rw [div_eq_mul_one_div, cardassum]; norm_num
        _ = ∑ (k : Fin (n + 1)), ↑(m k) * (1 / ↑(n.choose (n / 2))) := by rw [Finset.sum_mul]
        _ ≤ ∑ (k : Fin (n + 1)), ↑(m k) * (1 / ↑(n.choose k)) := by
          apply Finset.sum_le_sum
          intros k _
          rw [←div_eq_mul_one_div, ←div_eq_mul_one_div, div_le_div_iff]
          norm_cast
          apply mul_le_mul_left (m k)
          exact Nat.choose_le_middle k n
          · norm_num
            exact Nat.choose_pos (Nat.div_le_self n 2)
          · norm_num
            exact Nat.choose_pos (Nat.le_of_lt_succ k.isLt)
        _ = ∑ (k : Fin (n + 1)), (m k) * (k)! * (n - k)! * (1 / (n)! : ℚ) := by
          apply Finset.sum_congr
          rfl
          intro x _
          rw [Nat.choose_eq_factorial_div_factorial, mul_assoc, mul_assoc]
          congr
          rw [←mul_assoc, ←(div_helper (n)! (↑x)! (n - ↑x)!)]
          congr
          have xlen : ↑x ≤ n := Nat.le_of_lt_succ x.isLt

          have choose_divisibility (a b : ℕ) (h : a ≤ b) : ((a)! * (b - a)!) ∣ (b)! := by
            use b.choose a
            rw [Nat.mul_comm, ←Nat.mul_assoc]
            exact (Nat.choose_mul_factorial_mul_factorial h).symm

          rw [Nat.cast_div (choose_divisibility ↑x n xlen), Nat.cast_mul]
          · norm_num
            constructor <;> apply Nat.factorial_ne_zero
          · exact Nat.le_of_lt_succ x.isLt
        _ = (∑ (k : Fin (n + 1)), (m k) * (k)! * (n - k)!) * (1 / (n)! : ℚ) := by rw [←Finset.sum_mul]; norm_num
        _ ≤ (n)! * (1 / (n)! : ℚ) := by
          apply mul_le_mul
          exact cast_le.mpr central_inequality
          simp
          simp
          simp
        _ ≤ 1 := by field_simp

    have choose_pos : (0 : ℚ) < (n.choose (n / 2) : ℚ) := by
      apply cast_lt.mpr
      apply Nat.choose_pos
      apply Nat.div_le_self

    exact cast_le.mp ((div_le_one choose_pos).mp this)

end chapter30
