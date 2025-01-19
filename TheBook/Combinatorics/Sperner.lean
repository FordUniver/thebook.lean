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
import Mathlib.Data.Finset.Slice
import Mathlib.Order.Antichain
import Mathlib.Order.Chain

-- set_option maxHeartbeats 200000

/-!
# Proof of the LYM inequality and some observations on chains wrt the subset order
-/

open Function Finset Nat Set BigOperators

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)}

namespace Finset

/-
## Proposals for new definitions of chains in Finset namespace
-/

variable {β : Type*} (r : β → β → Prop)

/-- In this file, we use `≺` as a local notation for any relation `r`. -/
local infixl:50 " ≺ " => r

def IsChain (s : Finset β) : Prop :=
  s.toSet.Pairwise fun x y => x ≺ y ∨ y ≺ x

/-- `SuperChain s t` means that `t` is a chain that strictly includes `s`. -/
def SuperChain (s t : Finset β) : Prop :=
  IsChain r t ∧ s ⊂ t

/-- A chain `s` is a maximal chain if there does not exists a chain strictly including `s`. -/
def IsMaxChain (s :  Finset β) : Prop :=
  IsChain r s ∧ ∀ ⦃t⦄, IsChain r t → s ⊆ t → s = t

def IsAntichain (r : α → α → Prop) (s : Finset α) : Prop :=
  s.toSet.Pairwise rᶜ

end Finset

instance : Coe (IsChain (· ⊂ ·) 𝒜.toSet) (𝒜.IsChain (· ⊂ ·)) :=
  ⟨λ h => h⟩

instance : Coe (𝒜.IsChain (· ⊂ ·)) (IsChain (· ⊂ ·) 𝒜.toSet) :=
  ⟨λ h => h⟩

example (h : IsChain (· ⊂ ·) 𝒜.toSet) : 𝒜.IsChain (· ⊂ ·) := h
example (h : 𝒜.IsChain (· ⊂ ·)) : IsChain (· ⊂ ·) 𝒜.toSet := h

namespace Finset

structure MaxChainThrough (ℬ : Finset (Finset α)) where
  𝒜 : Finset (Finset α)
  isMaxChain : Finset.IsMaxChain (· ⊂ ·) 𝒜
  subChain : ℬ ⊆ 𝒜

def emb_MaxChainThrough (ℬ : Finset (Finset α)) (X : ℬ.MaxChainThrough) : Finset (Finset α) := X.𝒜

lemma inj_emb_MaxChainThrough (ℬ : Finset (Finset α)) : Injective (emb_MaxChainThrough ℬ) := by sorry

instance instFintypeMaxChainThrough {ℬ : Finset (Finset α)} : Fintype (MaxChainThrough ℬ) := by sorry

lemma IsChain.equivalence_subset_relations : (IsChain (· ⊆ .) 𝒜) ↔ (IsChain (· ⊂ .) 𝒜) := by
  constructor
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ => left; exact Finset.ssubset_iff_subset_ne.mpr ⟨e₁sube₂, e₁neqe₂⟩
    | inr e₂sube₁ => right; exact Finset.ssubset_iff_subset_ne.mpr ⟨e₂sube₁, e₁neqe₂.symm⟩
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ => left; exact e₁sube₂.left
    | inr e₂sube₁ => right; exact e₂sube₁.left

lemma IsMaxChain.equivalence_subset_relations : (IsMaxChain (· ⊆ .) 𝒜) ↔ (IsMaxChain (· ⊂ .) 𝒜) := by
  constructor
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mp h.left, fun t chain => h.right (IsChain.equivalence_subset_relations.mpr chain)⟩
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mpr h.left, fun t chain => h.right (IsChain.equivalence_subset_relations.mp chain)⟩

lemma SuperChain.equivalence_subset_relations {ℬ : Finset (Finset α)} : (SuperChain (· ⊆ .) ℬ 𝒜) ↔ (SuperChain (· ⊂ .) ℬ 𝒜) := by
  constructor
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mp h.left, h.right⟩
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mpr h.left, h.right⟩

/-- In a chain with respect to the subset order there can not be two sets of same cardinality -/
lemma IsChain.unique_of_cardinality_chain (chain𝒜 : IsChain (· ⊂ ·) 𝒜) {a b : Finset α}
    (amem : a ∈ 𝒜) (bmem : b ∈ 𝒜) (hcard : #a = #b) : a = b := by
  by_contra aneb
  cases chain𝒜 amem bmem aneb with
  | inl h =>
    have := Finset.card_strictMono h
    linarith
  | inr h =>
    have := Finset.card_strictMono h
    linarith

/-- In a chain with respect to the subset order there can be at most one set of a given cardinality -/
lemma IsChain.max_one_elt_chain_layer (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (j : ℕ) : #(𝒜 # j) ≤ 1 := by
  by_contra! ass
  have : (𝒜 # j) ≠ (∅ : Finset (Finset α)) := by
    intro assempty
    have := Finset.card_eq_zero.mpr assempty
    linarith
  obtain ⟨a, amem⟩ := Finset.nonempty_iff_ne_empty.mpr this
  obtain ⟨b, ⟨bmem, aneb⟩⟩ := Finset.exists_mem_ne ass a
  have cardeqab : #a = #b := by rw [(Finset.mem_slice.mp amem).right, (Finset.mem_slice.mp bmem).right]
  exact aneb (IsChain.unique_of_cardinality_chain chain𝒜 (Finset.slice_subset bmem) (Finset.slice_subset amem) cardeqab.symm)


instance IsChain.sub_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ⊆ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ => subset_trans h₁ h₂⟩

instance card_le : LE (Finset α) where
  le x y := #x ≤ #y

instance card_le_is_total : IsTotal 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ≤ e₂.val) :=
  ⟨fun a b ↦ Nat.le_total #a.val #b.val⟩

instance card_le_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ≤ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ ↦ Nat.le_trans h₁ h₂⟩

instance IsChain.card_le_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ⊆ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ => subset_trans h₁ h₂⟩

theorem List.nodup_insertionSort [LE α] [DecidableRel (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)]  {l : List α} (h : l.Nodup) : (l.insertionSort (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)).Nodup := by sorry

lemma IsChain.card_strict_mono (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : ((Finset.univ : Finset 𝒜).toList.insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val)).Sorted (fun (e₁ e₂ : 𝒜) ↦ #e₁.val < #e₂.val) := by
  apply List.pairwise_iff_get.mpr
  intro x y xlty
  let elt_x := ((List.insertionSort (fun (e₁ e₂ : 𝒜) => #e₁.val ≤ #e₂.val) univ.toList).get x)
  let elt_y := ((List.insertionSort (fun (e₁ e₂ : 𝒜) => #e₁.val ≤ #e₂.val) univ.toList).get y)
  have card_le : elt_x.val ≤ elt_y.val := List.pairwise_iff_get.mp (List.sorted_insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val) (Finset.univ : Finset 𝒜).toList) x y xlty
  by_contra! ass
  have card_eq := Nat.le_antisymm card_le ass

  have elt_x_eq_elt_y := Subtype.eq (IsChain.unique_of_cardinality_chain chain𝒜 elt_x.prop elt_y.prop card_eq)
  have elt_x_neq_elt_y : elt_x ≠ elt_y := List.pairwise_iff_get.mp (List.nodup_insertionSort ((Finset.univ : Finset 𝒜).nodup_toList)) x y xlty

  exact elt_x_neq_elt_y elt_x_eq_elt_y

/-- If a chain intersects a layer of the boolean lattice this intersection is a singleton -/
lemma layer_singleton_of_nonempty (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (j : Finset.range (n + 1)) (layer_nonempty : (𝒜 # j) ≠ ∅):
    ∃! e : Finset α, 𝒜 # j = {e} := by
  have : # (𝒜 # j) = 1 := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer chain𝒜 j) with
    | inl card_zero =>
      simp at card_zero
      exact False.elim (layer_nonempty card_zero)
    | inr card_one => exact card_one
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp this
  have unique : ∀ a : Finset α, 𝒜 # j = {a} → a = e := by
    intro a ha
    rw [he] at ha
    simp at ha
    exact ha.symm

  exact ⟨e, he, unique⟩

lemma IsChain.ssubset_of_lt_cardinality (chain𝒜 : IsChain (· ⊂ ·) 𝒜) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒜) (e₂mem : e₂ ∈ 𝒜)
    (hcard : #e₁ < #e₂) : e₁ ⊂ e₂ := by
  have e₁nee₂ : e₁ ≠ e₂ := by
    intro ass
    have : #e₁ = #e₂ := by rw [ass]
    linarith
  cases chain𝒜 e₁mem e₂mem e₁nee₂ with
  | inl h => exact Finset.ssubset_iff_subset_ne.mpr ⟨h.left, e₁nee₂⟩
  | inr h =>
    have : #e₂ < #e₁ := Finset.card_strictMono h
    linarith

lemma IsChain.subset_of_le_cardinality (chain𝒜 : IsChain (· ⊂ ·) 𝒜) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒜) (e₂mem : e₂ ∈ 𝒜)
    (hcard : #e₁ ≤ #e₂) : e₁ ⊆ e₂ := by
  cases Nat.eq_or_lt_of_le hcard with
  | inr hcard_lt =>
    exact (IsChain.ssubset_of_lt_cardinality chain𝒜 e₁mem e₂mem hcard_lt).left
  | inl hcard_eq =>
    exact Finset.subset_of_eq (IsChain.unique_of_cardinality_chain chain𝒜 e₁mem e₂mem hcard_eq)


variable [Fintype α] [DecidableEq α] [DecidableEq (Finset (Finset α))]

instance : Coe (Set (Finset α)) (Finset (Finset α)) :=
  ⟨λ s => by sorry⟩


example (ℬ : Set (Finset α)) : Finset (Finset α) := ℬ

def chain_extension_filter_function (𝒜 : Finset (Finset α)) (e : Finset α) : α → Prop :=
  fun a : α ↦ IsChain (· ⊂ ·) (insert (insert a e) 𝒜) ∧ insert a e ∉ 𝒜

instance instDecidableIsChain (𝒜 : Finset (Finset α)) : Decidable (IsChain (· ⊂ ·) 𝒜) := by
  sorry

instance instDecidablePredChainExtension (e : Finset α) :
    DecidablePred (chain_extension_filter_function 𝒜 e) :=
  fun a : α => inferInstanceAs (Decidable (IsChain (· ⊂ ·) (insert (insert a e) 𝒜) ∧ insert a e ∉ 𝒜))

lemma IsChain.empty_layer_by_card (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (card𝒜 : #𝒜 < n+1) : ∃ i : Fin (n + 1), #(𝒜 # i) = 0 := by
  by_contra! ass
  have : ∀ (i : Fin (n + 1)), #(𝒜 # i) = 1 := by
    intro i
    have non_zero := ass i
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer chain𝒜 i) with
    | inl h => exfalso; exact (non_zero h)
    | inr h => exact h
  rw [←sum_card_slice 𝒜] at card𝒜
  have := calc
    ∑ r ∈ Iic (Fintype.card α), #(𝒜 # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact this ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]
  linarith

lemma range_empty_layer (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (empty_layer : ∃ i : Fin (n + 1), #(𝒜 # i) = 0) (empty_elt : ∅ ∈ 𝒜) (univ_elt : Finset.univ ∈ 𝒜) :
    ∃ s : Fin (n + 1), ∃ t : Fin (n + 1), s.val + 2 ≤ t.val ∧ #(𝒜 # s) = 1 ∧ #(𝒜 # t) = 1 ∧ ∀ j : Fin (n + 1), s < j ∧ j < t → #(𝒜 # j) = 0 := by sorry

lemma mem_card_of_slice {ℬ : Finset (Finset α)} (h : (ℬ # s) = {layer_s}) : layer_s ∈ ℬ ∧ #layer_s = s := by
  have := Finset.mem_singleton_self layer_s
  rw [←h] at this
  simp [slice] at this
  exact this

lemma chain_extension (hn : Fintype.card α = n) {i j : Finset.range (n + 1)} (ilej_succ_succ : (i : ℕ) + 2 ≤ (j : ℕ)) (chain𝒜 : IsChain (· ⊂ ·) 𝒜)
    (hi : (𝒜 # i) = {layer_i}) (hj : (𝒜 # j) = {layer_j}) (emptylayer : ∀ l ∈ (Finset.range (n + 1)), i < l → l < j → #(𝒜 # l) = 0):
    Finset.filter (chain_extension_filter_function 𝒜 layer_i) (Finset.univ : Finset α) = layer_j \ layer_i := by
  have layer_j_mem_card := mem_card_of_slice hj
  have layer_i_mem_card := mem_card_of_slice hi

  ext x
  let e_new := insert x layer_i
  have he_new : e_new = insert x layer_i := rfl

  have e_new_card_lt_layer_j_card: #e_new < #layer_j := by
    rw [layer_j_mem_card.right]
    have : #e_new ≤ #layer_i + 1 := by
      simp only [e_new]
      exact Finset.card_insert_le x layer_i
    rw [layer_i_mem_card.right] at this
    apply Nat.lt_of_le_of_lt this
    exact Nat.succ_le_of_lt ilej_succ_succ

  constructor
  · intro hx
    simp [chain_extension_filter_function] at hx

    simp [←he_new] at hx
    have e_new_neq_layer_j : e_new ≠ layer_j := by
      intro ass
      have := layer_j_mem_card.left
      rw [←ass] at this
      exact hx.right this
    simp
    constructor
    · have e_new_mem : e_new ∈ insert e_new 𝒜 := by simp
      have layer_j_mem_insert : layer_j ∈ insert e_new 𝒜 := by
        simp
        right
        exact layer_j_mem_card.left
      have e_new_sub_layer_j := IsChain.subset_of_le_cardinality hx.left e_new_mem layer_j_mem_insert (Nat.le_of_lt e_new_card_lt_layer_j_card)
      rw [he_new] at e_new_sub_layer_j
      exact e_new_sub_layer_j (mem_insert_self x layer_i)
    · intro x_mem_layer_i
      have := layer_i_mem_card.left
      rw [←(Finset.insert_eq_self.mpr x_mem_layer_i)] at this
      exact hx.right this
  · intro hx
    simp at hx
    simp [chain_extension_filter_function]

    have case_helper {e₁ e₂ : Finset α} (e₁neqe₂ : e₁ ≠ e₂) (e₂_not_new : e₂ ∈ 𝒜) (e₁_new : e₁ = e_new) : e₁ ⊂ e₂ ∨ e₂ ⊂ e₁ := by
      have := chain𝒜 layer_i_mem_card.left e₂_not_new
      by_cases h : layer_i = e₂
      · right
        rw [←h, e₁_new, he_new]
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · simp
        · exact (Finset.insert_ne_self.mpr hx.right).symm
      · cases chain𝒜 e₂_not_new layer_i_mem_card.left (fun q => h q.symm) with
        | inl e₂_sub_layer_i =>
          right
          simp at e₂_sub_layer_i
          rw [e₁_new, he_new]
          refine' Finset.ssubset_of_ssubset_of_subset e₂_sub_layer_i _
          apply Finset.subset_insert
        | inr layer_i_sub_e₂ =>
          simp at layer_i_sub_e₂
          left
          by_contra e₂_sub_e₁

          have e₁_sub_e₂ : e₁ ⊆ e₂ := by
            rw [e₁_new, he_new]
            have layer_j_card_le_e₂_card : #layer_j ≤ #e₂ := by
              rw [layer_j_mem_card.right]
              by_contra!
              have e₂_card_gt_i : #e₂ > ↑i := by
                rw [←layer_i_mem_card.right]
                exact Finset.card_strictMono layer_i_sub_e₂
              have e₂_card_lt_n_succ : #e₂ < n + 1 := by
                apply Nat.lt_succ_of_le
                rw [←hn]
                apply Finset.card_le_univ
              have e₂_empty_layer := emptylayer #e₂ (by simp; exact e₂_card_lt_n_succ) e₂_card_gt_i this
              simp at e₂_empty_layer
              have : e₂ ∈ 𝒜 # #e₂ := by simpa [slice]
              simp [e₂_empty_layer] at this

            have layer_j_sub_e₂ := IsChain.subset_of_le_cardinality chain𝒜 layer_j_mem_card.left e₂_not_new layer_j_card_le_e₂_card

            apply Finset.insert_subset
            · exact layer_j_sub_e₂ hx.left
            · have : #layer_i ≤ #e₂ := by
                rw [layer_i_mem_card.right]
                rw [layer_j_mem_card.right] at layer_j_card_le_e₂_card
                exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_succ_lt ilej_succ_succ)) layer_j_card_le_e₂_card

              exact IsChain.subset_of_le_cardinality chain𝒜 layer_i_mem_card.left e₂_not_new this

          have : ¬(e₁ ⊆ e₂ ∧ e₁ ≠ e₂) := fun q => e₂_sub_e₁ (Finset.ssubset_iff_subset_ne.mpr q)
          simp at this
          exact e₁neqe₂ (this e₁_sub_e₂)

    constructor
    · intro e₁ e₁mem e₂ e₂mem e₁neqe₂
      simp [←he_new] at e₁mem e₂mem
      simp
      cases e₁mem with
      | inl e₁_new =>
        cases e₂mem with
        | inl e₂_new =>
          rw [←e₂_new] at e₁_new
          left
          exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_of_eq e₁_new, e₁neqe₂⟩
        | inr e₂_not_new =>
          exact case_helper e₁neqe₂ e₂_not_new e₁_new
      | inr e₁_not_new =>
        cases e₂mem with
        | inl e₂_new =>
          apply Or.symm
          exact case_helper e₁neqe₂.symm e₁_not_new e₂_new
        | inr e₂_not_new =>
          exact chain𝒜 e₁_not_new e₂_not_new e₁neqe₂

    · intro e_new_mem_𝒜
      have e_new_card_gt_layer_i : #e_new > i := by simp [Finset.card_insert_of_not_mem hx.right, layer_i_mem_card.right]

      rw [layer_j_mem_card.right] at e_new_card_lt_layer_j_card
      have : #(𝒜 # #e_new) = 0 := by
        refine' emptylayer #e_new _ e_new_card_gt_layer_i e_new_card_lt_layer_j_card
        · simp
          exact Nat.lt_trans e_new_card_lt_layer_j_card (mem_range.mp j.property)
      have : (𝒜 # #e_new).Nonempty := by
        have : e_new ∈ 𝒜 # #e_new := by simpa [slice]
        exact nonempty_of_mem this
      have : #(𝒜 # #e_new) > 0 := Finset.card_pos.mpr this
      linarith

lemma one_elt_max_chain_layer (hn : Fintype.card α = n) (maxchain𝒜 : IsMaxChain (· ⊂ ·) 𝒜) (j : Finset.range (n + 1)) : #(𝒜 # j) = 1 := by
  by_contra! ass
  have empty_layer : 𝒜 # j = ∅ := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer maxchain𝒜.left j) with
    | inl h => simp at h; exact h
    | inr h => omega

  if htop : ∀ i : Finset.range (n + 1), i > j → 𝒜 # i = ∅ then
    have univnotin𝒜 : (Finset.univ : Finset α) ∉ 𝒜 := by
      intro ass₂
      have nslicemem : (Finset.univ : Finset α) ∈ 𝒜 # n := by
        simp [Finset.slice]
        exact ⟨ass₂, hn⟩
      cases Nat.lt_or_ge j n with
      | inl jltn =>
        have nsliceempty : 𝒜 # n = ∅ := htop ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩ jltn
        simp [nsliceempty] at nslicemem
      | inr jgen =>
        have jeqn : j = n := Nat.eq_of_le_of_lt_succ jgen (Finset.mem_range.1 (by simp))
        rw [jeqn] at empty_layer
        simp [empty_layer] at nslicemem
    simp [IsMaxChain] at maxchain𝒜
    have larger_chain_with_univ' : _root_.IsChain (· ⊂ ·) (Insert.insert (Finset.univ : Finset α) 𝒜).toSet := by
      have : ((Insert.insert (Finset.univ : Finset α) 𝒜) : Finset (Finset α)).toSet = ((Insert.insert (Finset.univ : Finset α) 𝒜) : Set (Finset α)) := by simp
      rw [this]
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun h => bneq h.symm⟩

    have larger_chain_with_univ : Finset.IsChain (· ⊂ ·) ((Insert.insert (Finset.univ : Finset α) 𝒜) : Finset (Finset α)) := larger_chain_with_univ'

    have univin𝒜 := Finset.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_univ (by simp)).symm
    exact univnotin𝒜 univin𝒜
  else if hbottom : ∀ i : Finset.range (n + 1), i < j → 𝒜 # i = ∅ then
    have emptynotin𝒜 : (∅ : Finset α) ∉ 𝒜 := by
      intro ass₃
      have zeroslicemem : (∅ : Finset α) ∈ 𝒜 # 0 := by
        simp [Finset.slice]
        exact ass₃
      cases Nat.eq_zero_or_pos j with
      | inl jeqzero =>
        rw [jeqzero] at empty_layer
        simp [empty_layer] at zeroslicemem
      | inr jgen =>
        simp [hbottom ⟨0, by simp⟩ jgen] at zeroslicemem
    simp [IsMaxChain] at maxchain𝒜
    have larger_chain_with_empty' : _root_.IsChain (· ⊂ ·) ((Insert.insert (∅ : Finset α) 𝒜)).toSet := by
      have : ((Insert.insert (∅ : Finset α) 𝒜)).toSet = (Insert.insert (∅ : Finset α) 𝒜.toSet) := by simp
      rw [this]
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, bneq⟩

    have larger_chain_with_empty : IsChain (· ⊂ ·) ((Insert.insert (∅ : Finset α) 𝒜)) := larger_chain_with_empty'

    have emptyin𝒜 := Finset.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_empty (by simp)).symm
    exact emptynotin𝒜 emptyin𝒜

  else
    simp at htop hbottom
    let indices_nonempty_top := Finset.filter (fun i : Finset.range (n + 1) ↦ i > j ∧ 𝒜 # i ≠ ∅) (Finset.univ : Finset (Finset.range (n + 1)))
    let indices_nonempty_bottom := Finset.filter (fun i : Finset.range (n + 1) ↦ i < j ∧ 𝒜 # i ≠ ∅) (Finset.univ : Finset (Finset.range (n + 1)))
    have nonempty_indices_nonempty_top : indices_nonempty_top.Nonempty := by
      simp [Finset.Nonempty]
      obtain ⟨i, ⟨⟨ilen, jlti⟩, jlayernotempty⟩⟩ := htop
      use i
      simp [indices_nonempty_top]
      constructor
      · use ilen
      · exact jlayernotempty

    have nonempty_indices_nonempty_bottom : indices_nonempty_bottom.Nonempty := by
      simp [Finset.Nonempty]
      obtain ⟨i, ⟨⟨ilen, iltj⟩, jlayernotempty⟩⟩ := hbottom
      use i
      simp [indices_nonempty_bottom]
      constructor
      · use ilen
      · exact jlayernotempty

    obtain ⟨s_top, s_top_min⟩ := Finset.min_of_nonempty nonempty_indices_nonempty_top
    have h_s_top := Finset.mem_of_min s_top_min
    simp [indices_nonempty_top] at h_s_top

    obtain ⟨s_bottom, s_bottom_max⟩ := Finset.max_of_nonempty nonempty_indices_nonempty_bottom
    have h_s_bottom := Finset.mem_of_max s_bottom_max
    simp [indices_nonempty_bottom] at h_s_bottom

    have emptylayer : ∀ l ∈ (Finset.range (n + 1)), s_bottom < l → l < s_top → #(𝒜 # l) = 0 := by
      intro l lmem s_bottom_lt_l l_lt_s_top

      have h_top : ⟨l, lmem⟩ ∉ indices_nonempty_top := Finset.not_mem_of_lt_min l_lt_s_top s_top_min
      have h_bottom : ⟨l, lmem⟩ ∉ indices_nonempty_bottom := Finset.not_mem_of_max_lt s_bottom_lt_l s_bottom_max

      simp [indices_nonempty_top] at h_top
      simp [indices_nonempty_bottom] at h_bottom

      simp

      by_cases jeql : j = ⟨l, lmem⟩
      · rw [←empty_layer, jeql]
      · cases (Nat.lt_or_gt_of_ne (fun ass : ↑j = l => jeql (by simp [←ass]))) with
        | inl jltl => exact h_top jltl
        | inr jgtl => exact h_bottom jgtl

    obtain ⟨e_bottom, ⟨bottom_singleton : 𝒜 # s_bottom = {e_bottom}, _⟩⟩ := layer_singleton_of_nonempty maxchain𝒜.left s_bottom h_s_bottom.right

    obtain ⟨e_top, ⟨top_singleton : 𝒜 # s_top = {e_top}, _⟩⟩ := layer_singleton_of_nonempty maxchain𝒜.left s_top h_s_top.right

    let extension_candidates := Finset.filter (chain_extension_filter_function 𝒜 e_bottom) (Finset.univ : Finset α)

    have extension_candidates_eq : extension_candidates = e_top \ e_bottom := by
      refine' chain_extension hn _ maxchain𝒜.left bottom_singleton top_singleton emptylayer
      apply Nat.succ_le_of_lt
      have : (s_bottom : ℕ) + 1 ≤ ↑j := Nat.succ_le_of_lt h_s_bottom.left
      exact Nat.lt_of_le_of_lt this h_s_top.left
    simp at extension_candidates_eq

    have e_bottom_mem_card : e_bottom ∈ 𝒜 ∧ #e_bottom = s_bottom := by
      have := Finset.mem_singleton_self e_bottom
      rw [←bottom_singleton] at this
      simp [slice] at this
      exact this

    have e_top_mem_card : e_top ∈ 𝒜 ∧ #e_top = s_top := by
      have := Finset.mem_singleton_self e_top
      rw [←top_singleton] at this
      simp [slice] at this
      exact this

    have extension_candidates_ne_empty : #extension_candidates > 0 := by
      rw [extension_candidates_eq]
      have card_bottom_lt_card_top : #e_bottom < #e_top := by
        rw [e_top_mem_card.right, e_bottom_mem_card.right]
        exact Nat.lt_trans h_s_bottom.left h_s_top.left
      have bottom_subset_top : e_bottom ⊂ e_top :=
        IsChain.ssubset_of_lt_cardinality maxchain𝒜.left e_bottom_mem_card.left e_top_mem_card.left card_bottom_lt_card_top
      have := Finset.card_sdiff_add_card_eq_card bottom_subset_top.left
      linarith
    simp at extension_candidates_ne_empty
    obtain ⟨a, ha⟩ := extension_candidates_ne_empty
    simp [extension_candidates, chain_extension_filter_function] at ha
    have := Finset.insert_eq_self.mp (maxchain𝒜.right ha.left (by simp)).symm
    exact ha.right this

lemma IsMaxChain.card {ℬ : Finset (Finset α)} (hn : Fintype.card α = n) (maxChainℬ : IsMaxChain (· ⊂ ·) ℬ) : ℬ.card = n + 1 := by
  rw [←sum_card_slice ℬ]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(ℬ # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact one_elt_max_chain_layer hn maxChainℬ ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsChain.card_le {ℬ : Finset (Finset α)} (hn : Fintype.card α = n) (chainℬ : IsChain (· ⊂ ·) ℬ) : ℬ.card ≤ n + 1 := by
  rw [←sum_card_slice ℬ]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(ℬ # r) ≤ ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply sum_le_sum
      intro j jmem
      exact IsChain.max_one_elt_chain_layer chainℬ j
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsMaxChain.iff_card {ℬ : Finset (Finset α)} (hn : Fintype.card α = n) (chainℬ : IsChain (· ⊂ ·) ℬ) : IsMaxChain (· ⊂ ·) ℬ ↔ ℬ.card = n + 1 := by
  constructor
  · intro maxChainℬ
    exact IsMaxChain.card hn maxChainℬ
  · intro cardℬ
    constructor
    · exact chainℬ
    · intro 𝒜 chain𝒜 ℬssub𝒜
      have hcard𝒜 : #𝒜 ≤ #ℬ := by
        · rw [cardℬ]
          exact IsChain.card_le hn chain𝒜
      exact (Finset.subset_iff_eq_of_card_le hcard𝒜).mp ℬssub𝒜

lemma card_maxChainThrough {ℬ : Finset (Finset α)} (hn : Fintype.card α = n) (chain : MaxChainThrough ℬ) : #chain.𝒜 = n + 1 := by
  rw [←sum_card_slice chain.𝒜]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(chain.𝒜 # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact one_elt_max_chain_layer hn chain.isMaxChain ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma incident_indices_monotone_cards {n: ℕ} {s t : Fin (n + 1)} {ℬ : Finset (Finset α)} (ilej_succ_succ : s.val + 2 ≤ t.val)
    (monotone_cards: StrictMono (fun i : Fin ℬ.toList.length ↦ (ℬ.toList[i.val]).card))
    (hs : (ℬ # s) = {layer_s}) (ht : (ℬ # t) = {layer_t})
    (empty_layer : ∀ j : Fin (n + 1), s < j → j < t → #(ℬ # ↑j) = 0) :
    ∃ i_s : Fin (ℬ.toList.length - 1), ℬ.toList[i_s.val]  = layer_s ∧ ℬ.toList[i_s.val + 1] = layer_t := by

  let i_s := ℬ.toList.indexOf layer_s
  have i_s_in_range : i_s < ℬ.toList.length := List.indexOf_lt_length.mpr (mem_toList.mpr (mem_card_of_slice hs).left)
  have h_i_s : ℬ.toList[i_s] = layer_s := ℬ.toList.indexOf_get i_s_in_range

  let i_t := ℬ.toList.indexOf layer_t
  have i_t_in_range : i_t < ℬ.toList.length := List.indexOf_lt_length.mpr (mem_toList.mpr (mem_card_of_slice ht).left)
  have h_i_t : ℬ.toList[i_t] = layer_t := ℬ.toList.indexOf_get i_t_in_range

  have i_s_eq_i_t_succ : i_t = i_s + 1 := by
    by_contra ass₁
    have : (⟨i_t, i_t_in_range⟩ : Fin ℬ.toList.length) > (⟨i_s, i_s_in_range⟩ : Fin ℬ.toList.length) := by
      by_contra! ass₂
      have := (StrictMono.monotone monotone_cards) ass₂
      simp only [h_i_s, h_i_t, (mem_card_of_slice hs).right, (mem_card_of_slice ht).right] at this
      linarith
    have i_s_succ_lt : i_s + 1 < i_t := Nat.lt_of_le_of_ne this fun a => ass₁ (id (Eq.symm a))

    let e := ℬ.toList[i_s + 1]

    have e_card_gt' : #e > s := by
      have : (⟨i_s, i_s_in_range⟩ : Fin ℬ.toList.length) < (⟨i_s + 1, Nat.lt_trans i_s_succ_lt i_t_in_range⟩ : Fin ℬ.toList.length) := by simp
      have := monotone_cards this
      simp only [h_i_s, (mem_card_of_slice hs).right] at this
      exact this

    have e_card_lt' : #e < t := by
      have : (⟨i_t, i_t_in_range⟩ : Fin ℬ.toList.length) > (⟨i_s + 1, Nat.lt_trans i_s_succ_lt i_t_in_range⟩ : Fin ℬ.toList.length) := by simp [i_s_succ_lt]
      have := monotone_cards this
      simp only [h_i_t, (mem_card_of_slice ht).right] at this
      exact this

    have card_e_mod : #e % (n + 1) = #e := mod_eq_of_lt (Nat.lt_trans e_card_lt' t.is_lt)

    have e_card_gt : Fin.ofNat #e > s := by simp [Fin.ofNat, card_e_mod]; exact e_card_gt'
    have e_card_lt : Fin.ofNat #e < t := by simp [Fin.ofNat, card_e_mod]; exact e_card_lt'


    have layer_empty := empty_layer (Fin.ofNat #e) e_card_gt e_card_lt

    have layer_nonempty : e ∈ (ℬ # ↑(Fin.ofNat #e : Fin (n + 1))) := by
      simp [mem_slice]
      constructor
      · apply mem_toList.mp
        exact List.get_mem ℬ.toList (i_s + 1) (Nat.lt_trans i_s_succ_lt i_t_in_range)
      · simp [Fin.ofNat, card_e_mod]

    simp at layer_empty

    simp [layer_empty] at layer_nonempty

  have i_s_upperbound : i_s < ℬ.toList.length - 1 :=
    have : i_s + 1 < ℬ.toList.length := by rw [←i_s_eq_i_t_succ]; exact i_t_in_range
    lt_sub_of_add_lt this

  use ⟨i_s, i_s_upperbound⟩

  simp only [i_s_eq_i_t_succ] at h_i_t

  exact ⟨h_i_s, h_i_t⟩

lemma count_maxChainsThrough {n: ℕ} (m : ℕ) (h_mn : m ≤ n + 1) (hn : Fintype.card α = n)
    (ℬ : Finset (Finset α)) (cardℬ : #ℬ = m) (chainℬ : IsChain (· ⊂ ·) ℬ)
    (monotone_cards: StrictMono (fun (i : Fin ℬ.toList.length) ↦ #ℬ.toList[i])) (empty_in_chain : ∅ ∈ ℬ) (univ_in_chain : univ ∈ ℬ) :
    Fintype.card (ℬ.MaxChainThrough) = ∏ j : Fin (ℬ.toList.length - 1), (#ℬ.toList[j.val + 1] - #ℬ.toList[j.val])! := by
  revert ℬ
  induction' h_mn using decreasingInduction with n_ q ih
  · intro ℬ cardℬ chainℬ monotone_cards empty_in_chain univ_in_chain

    obtain ⟨s', t', empty_range : s'.val + 2 ≤ t'.val ∧ #(ℬ # s') = 1 ∧ #(ℬ # t') = 1 ∧ ∀ (j : Fin (n + 1)), s' < j ∧ j < t' → #(ℬ # ↑j) = 0⟩ :=
      range_empty_layer hn chainℬ (IsChain.empty_layer_by_card hn chainℬ (lt_of_eq_of_lt cardℬ q)) empty_in_chain univ_in_chain

    let s : Finset.range (n + 1) := ⟨s'.val, mem_range.mpr s'.is_lt⟩
    let t : Finset.range (n + 1) := ⟨t'.val, mem_range.mpr t'.is_lt⟩

    have ilej_succ_succ : (s : ℕ) + 2 ≤ (t : ℕ) := by simp [empty_range.left]

    obtain ⟨layer_t, ht : (ℬ # t) = {layer_t}⟩ := Finset.card_eq_one.mp empty_range.right.right.left
    obtain ⟨layer_s, hs : (ℬ # s) = {layer_s}⟩ := Finset.card_eq_one.mp empty_range.right.left

    have empty_layer' : ∀ j ∈ Finset.range (n + 1), s < j → j < t → #(ℬ # ↑j) = 0 := by
      simp
      intro j jinrange jgt jlt

      have nsuccnezero : n + 1 ≠ 0 := by simp
      have jmod : j % (n + 1) = j := (mod_eq_iff_lt nsuccnezero).mpr jinrange
      have s'ltj : s' < Fin.ofNat j := by simp [Fin.ofNat, jmod]; exact jgt
      have jltt' : Fin.ofNat j < t' := by simp [Fin.ofNat, jmod]; exact jlt
      have := empty_range.right.right.right j ⟨s'ltj, jltt'⟩
      simp [jmod] at this
      exact this

    have empty_layer : ∀ j : Fin (n + 1), s' < j → j < t' → #(ℬ # ↑j) = 0 := by
      simp
      intro j jgt jlt

      have nsuccnezero : n + 1 ≠ 0 := by simp
      have := empty_range.right.right.right j ⟨jgt, jlt⟩
      simp at this
      exact this

    let extension_candidates := Finset.filter (chain_extension_filter_function ℬ layer_s) (Finset.univ : Finset α)

    have extension_candidates_eq : extension_candidates = layer_t \ layer_s := by
      refine' chain_extension hn ilej_succ_succ chainℬ hs ht empty_layer'

    have layer_s_mem_card := mem_card_of_slice hs
    have layer_t_mem_card := mem_card_of_slice ht

    obtain ⟨i_s, ⟨entry_i_s, entry_i_s_succ⟩⟩ := incident_indices_monotone_cards ilej_succ_succ monotone_cards hs ht empty_layer

    have i_s_in_range : i_s < ℬ.toList.length := Nat.lt_of_lt_of_le i_s.is_lt (Nat.pred_le ℬ.toList.length)
    have i_s_succ_in_range : i_s.val + 1 < ℬ.toList.length := add_lt_of_lt_sub i_s.is_lt

    let multiplicant' (j : Fin (ℬ.toList.length - 1)) : ℕ := (#ℬ.toList[j.val + 1] - #ℬ.toList[j.val] - 1)!
    let multiplicant (j : Fin (ℬ.toList.length - 1)) : ℕ := (#ℬ.toList[j.val + 1] - #ℬ.toList[j.val])!

    have extension_candidates_card : #extension_candidates = #ℬ.toList[i_s.val + 1] - #ℬ.toList[i_s.val] := by
      rw [entry_i_s, entry_i_s_succ, layer_s_mem_card.right, layer_t_mem_card.right]
      rw [extension_candidates_eq]
      have card_bottom_lt_card_top : #layer_s < #layer_t := by
        rw [layer_s_mem_card.right, layer_t_mem_card.right]
        linarith
      have bottom_subset_top : layer_s ⊂ layer_t :=
        IsChain.ssubset_of_lt_cardinality chainℬ layer_s_mem_card.left layer_t_mem_card.left card_bottom_lt_card_top
      have := Finset.card_sdiff_add_card_eq_card bottom_subset_top.left
      rw [←layer_s_mem_card.right, ←layer_t_mem_card.right]
      exact Nat.eq_sub_of_add_eq this

    let 𝒬 := (Finset.univ : Finset (Fin (ℬ.toList.length - 1)))
    let 𝒬' := 𝒬 \ {i_s}

    let extensions_wrt (x : α) : Finset (Finset (Finset α)) := by
      let ℬ' : Finset (Finset α) := Insert.insert (Insert.insert x layer_s) ℬ
      exact (Finset.univ : Finset ℬ'.MaxChainThrough).image (emb_MaxChainThrough ℬ')

    /- Here the induction hypothesis ih is applied-/
    have card_extensions_wrt (a : extension_candidates) : #(extensions_wrt a) = (multiplicant' i_s) * ∏ j ∈ 𝒬', (multiplicant j) := by
      let e_new := Insert.insert (↑a) layer_s
      let ℬ' := (Insert.insert e_new ℬ)

      have a_property₁ := a.prop
      simp only [extension_candidates, mem_filter, chain_extension_filter_function] at a_property₁

      have a_property₂ := a.prop
      simp [extension_candidates_eq] at a_property₂

      have card_e_new : #e_new = s + 1 := by
        have := layer_s_mem_card.right
        simp [s] at this
        simp [e_new, ←this]
        apply card_insert_of_not_mem
        · exact a_property₂.right

      have ℬ'card : #ℬ' = n_ + 1 := by
        simp [ℬ', ←cardℬ]
        apply Finset.card_insert_of_not_mem
        · exact a_property₁.right.right

      have monotone_cards' : StrictMono (fun (i : Fin ℬ'.toList.length) ↦ #ℬ'.toList[i]) := by sorry

      have := Finset.card_image_of_injective (Finset.univ : Finset (MaxChainThrough ℬ')) (inj_emb_MaxChainThrough ℬ')
      simp [extensions_wrt, this]

      have empty_in_chain' : ∅ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr empty_in_chain)
      have univ_in_chain' : univ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr univ_in_chain)

      let i_new := ℬ'.toList.indexOf e_new
      have i_new_in_range : i_new < ℬ'.toList.length := List.indexOf_lt_length.mpr (mem_toList.mpr (mem_insert_self e_new ℬ))
      have h_i_new : ℬ'.toList[i_new] = e_new := ℬ'.toList.indexOf_get i_new_in_range

      let i_univ := ℬ'.toList.indexOf univ
      have i_univ_in_range : i_univ < ℬ'.toList.length := List.indexOf_lt_length.mpr (mem_toList.mpr univ_in_chain')
      have h_i_univ : ℬ'.toList[i_univ] = univ := ℬ'.toList.indexOf_get i_univ_in_range

      have i_new_lt_i_univ' : (⟨i_new, i_new_in_range⟩ : Fin ℬ'.toList.length) < (⟨i_univ, i_univ_in_range⟩ : Fin ℬ'.toList.length) := by
        by_contra! ass
        have := (StrictMono.monotone monotone_cards') ass
        simp [h_i_new, h_i_univ, card_e_new, hn] at this
        linarith [empty_range.left, t'.is_lt]

      have i_new_lt_i_univ_pred : i_new < ℬ'.toList.length - 1 := Nat.lt_of_lt_of_le i_new_lt_i_univ' (Nat.le_pred_of_lt i_univ_in_range)

      let i_new' : Fin (ℬ'.toList.length - 1) := ⟨i_new, i_new_lt_i_univ_pred⟩
      have h_i_new' : i_new' ∈ (Finset.univ : Finset (Fin (ℬ'.toList.length - 1))) := by simp

      have ind_present := ih ℬ' ℬ'card a_property₁.right.left monotone_cards' empty_in_chain' univ_in_chain'

      have product_split := Finset.prod_eq_mul_prod_diff_singleton h_i_new' (fun (i : Fin (ℬ'.toList.length - 1)) ↦ (#ℬ'.toList[i.val + 1] - #ℬ'.toList[i.val])!)

      rw [ind_present, product_split]

      have prod_identity : ∏ j ∈ 𝒬', multiplicant j = ∏ x ∈ univ \ {i_new'}, (#ℬ'.toList[↑x + 1] - #ℬ'.toList[↑x])! := by
        simp [𝒬', multiplicant]
        sorry

      have mul_identity : multiplicant' i_s = (#ℬ'.toList[↑i_new' + 1] - #ℬ'.toList[↑i_new'])! := by sorry

      rw [prod_identity, mul_identity]


    /-The set of maximal chains through ℬ is the disjoint union of maximal chains through the union of ℬ with some chain extension candidate-/
    have central_identity: (Finset.univ : Finset ℬ.MaxChainThrough).image (emb_MaxChainThrough ℬ) = extension_candidates.disjiUnion extensions_wrt (by sorry) := by sorry

    have := Finset.card_image_of_injective (Finset.univ : Finset ℬ.MaxChainThrough) (inj_emb_MaxChainThrough ℬ)

    rw [Fintype.card, ←this, central_identity, card_disjiUnion]

    calc
      ∑ a ∈ extension_candidates, #(extensions_wrt a) =
          ∑ a ∈ extension_candidates, (multiplicant' i_s) * ∏ j ∈ 𝒬', (multiplicant j) := by
        apply sum_congr (by simp)
        intro x hx
        exact card_extensions_wrt ⟨x, hx⟩
      _ = (multiplicant i_s) *  ∏ j ∈ 𝒬', (multiplicant j) := by
        simp [Finset.sum_const, extension_candidates_card, multiplicant']
        rw [←mul_assoc]
        congr
        simp [multiplicant]
        apply mul_factorial_pred _
        · simp [entry_i_s, entry_i_s_succ, layer_s_mem_card.right, layer_t_mem_card.right]
          have : s'.val < t'.val := by linarith [empty_range.left]
          exact this
      _ = (multiplicant i_s) *  ∏ j ∈ 𝒬', (multiplicant j) := by simp
      _ = ∏ j ∈ 𝒬, (multiplicant j) := by
        simp [𝒬']
        have : i_s ∈ 𝒬 := by simp [𝒬]
        exact (Finset.prod_eq_mul_prod_diff_singleton this multiplicant).symm
      _ = ∏ j ∈ 𝒬, (#ℬ.toList[j.val + 1] - #ℬ.toList[j.val])! := by
        apply prod_congr (by simp)
        intro x hx
        rfl

  · intro ℬ cardℬ chainℬ monotone_cards empty_in_chain univ_in_chain
    have entry_cards : ∀ j : Fin (ℬ.toList.length - 1), #ℬ.toList[j.val] = j.val := by sorry
    have rhs_one := by calc
      ∏ j : Fin (ℬ.toList.length - 1), (#ℬ.toList[j.val + 1] - #ℬ.toList[j.val])! = ∏ j : Fin (ℬ.toList.length - 1), 1 := by
        apply Finset.prod_congr (by simp)
        intro j _
        rw [entry_cards, entry_cards ⟨j + 1, by sorry⟩]
        simp
      _ = 1 := Fintype.prod_eq_one (fun a => 1) (congrFun rfl)
    rw [rhs_one, Fintype.card_eq_one_iff]
    have ℬmaxChain := (IsMaxChain.iff_card hn chainℬ).mpr cardℬ
    use {
      𝒜 := ℬ,
      isMaxChain := ℬmaxChain,
      subChain := by simp
    }
    intro X
    have same_elements : X.𝒜 = ℬ := (ℬmaxChain.right X.isMaxChain.left X.subChain).symm
    rcases X with ⟨X.𝒜, b, c⟩
    simpa

lemma count_maxChains_through_singleton (e : Finset α) (hn : Fintype.card α = n): Fintype.card (MaxChainThrough {e}) = (#e)! * (n - #e)! := by sorry

/-- The **Lubell-Yamamoto-Meshalkin inequality**. Sperner's Theorem follows as in Mathlib.Combinatorics.SetFamily.LYM as a corollary -/
theorem lym_inequality (antichain𝒜 : IsAntichain (· ⊂ ·) 𝒜) (hn : Fintype.card α = n):
    ∑ k ∈ Iic n, #(𝒜 # k) / (n.choose k : ℚ) ≤ (1 : ℚ) := by
  have : ∑ k ∈ Iic n, #(𝒜 # k) / (n.choose k : ℚ) ≤ (∑ k ∈ Iic n, #(𝒜 # k) * (k)! * (n - k)!) * (1 / (n)! : ℚ) := by
    calc
      ∑ k ∈ Iic n, #(𝒜 # k) / (n.choose k : ℚ) = ∑ k ∈ Iic n, #(𝒜 # k) * (k)! * (n - k)! * (1 / (n)! : ℚ) := by
        apply Finset.sum_congr (by simp)
        intro j jmem
        simp at jmem
        rw [div_eq_mul_inv, mul_assoc, mul_assoc, Nat.choose_eq_factorial_div_factorial]
        congr
        field_simp

        have choose_divisibility (a b : ℕ) (h : a ≤ b) : ((a)! * (b - a)!) ∣ (b)! := by
          use b.choose a
          rw [Nat.mul_comm, ←Nat.mul_assoc]
          exact (Nat.choose_mul_factorial_mul_factorial h).symm

        rw [Nat.cast_div (choose_divisibility j n jmem), Nat.cast_mul]
        · field_simp
        · norm_num
          constructor <;> apply Nat.factorial_ne_zero
        · exact jmem
      _ = (∑ k ∈ Iic n, #(𝒜 # k) * (k)! * (n - k)!) * (1 / (n)! : ℚ) := by simp [←Finset.sum_mul]
    rfl

  refine' le_trans this _
  rw [mul_one_div]
  apply (div_le_one (by simp [Nat.factorial_pos n])).mpr

  norm_cast

  have slice_partition : Finset.disjiUnion (Iic n) 𝒜.slice (Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)) = 𝒜 := by
    rw [Finset.disjiUnion_eq_biUnion (Iic n) 𝒜.slice (Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _))]
    rw [←hn]
    simp [biUnion_slice 𝒜]

  calc
    ∑ k ∈ Iic n, #(𝒜 # k) * (k)! * (n - k)! = ∑ k ∈ Iic n, ∑ e ∈ (𝒜 # k), (#e)! * (n - #e)! := by
      apply Finset.sum_congr (by simp)
      intro k _
      have hq : ∀ e ∈ (𝒜 # k), (#e)! * (n - #e)! = (k)! * (n - k)! := by
        intro e he
        simp [slice] at he
        rw [he.2]
      rw [Finset.sum_congr rfl hq, Finset.sum_const]
      ring
    _ = ∑ e ∈ 𝒜, (#e)! * (n - #e)! := by
      conv =>
        rhs
        rw [←slice_partition]
      apply Eq.symm
      apply sum_disjiUnion
    _ = ∑ e ∈ 𝒜, Fintype.card (MaxChainThrough {e}) := by
      apply Finset.sum_congr (by simp)
      intro e _
      apply Eq.symm
      exact count_maxChains_through_singleton e hn
    _ ≤ (n)! := by sorry
    --here one must embedd the chains into some common space for counting as solved in 'Sperner_handcrafted_definitions.lean' with the function 'f_embedded_chains'
