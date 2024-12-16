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

/-!
# Proof of the LYM inequality and some observations on chains wrt the subset order
-/

open Function Finset Nat Set BigOperators

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)} {𝒞 : Set (Finset α)}

namespace Finset

structure MaxChainThrough (ℬ : Finset (Finset α)) where
  𝒜 : Finset (Finset α)
  isMaxChain : IsMaxChain (· ⊂ ·) (𝒜 : Set (Finset α))
  superChain : SuperChain (· ⊂ ·) (ℬ : Set (Finset α)) (𝒜 : Set (Finset α))

instance instFintypeMaxChainThrough {ℬ : Finset (Finset α)} : Fintype (MaxChainThrough ℬ) := by sorry

lemma IsChain.equivalence_subset_relations : (IsChain (· ⊆ .) 𝒞) ↔ (IsChain (· ⊂ .) 𝒞) := by
  constructor
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ =>
      left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨e₁sube₂, e₁neqe₂⟩
    | inr e₂sube₁ =>
      right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨e₂sube₁, e₁neqe₂.symm⟩
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ =>
      left
      exact e₁sube₂.left
    | inr e₂sube₁ =>
      right
      exact e₂sube₁.left

lemma IsMaxChain.equivalence_subset_relations : (IsMaxChain (· ⊆ .) 𝒞) ↔ (IsMaxChain (· ⊂ .) 𝒞) := by sorry
lemma SuperChain.equivalence_subset_relations {ℬ : Finset (Finset α)} : (SuperChain (· ⊆ .) ℬ 𝒞) ↔ (SuperChain (· ⊂ .) ℬ 𝒞) := by sorry

/-- In a chain with respect to the subset order there can not be two sets of same cardinality -/
lemma IsChain.unique_of_cardinality_chain (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {a b : Finset α}
    (amem : a ∈ 𝒞) (bmem : b ∈ 𝒞) (hcard : a.card = b.card) : a = b := by
  by_contra aneb
  cases chain𝒞 amem bmem aneb with
  | inl h =>
    have := Finset.card_strictMono h
    linarith
  | inr h =>
    have := Finset.card_strictMono h
    linarith

/-- In a chain with respect to the subset order there can be at most one set of a given cardinality -/
lemma IsChain.max_one_elt_chain_layer (chain𝒜 : IsChain (· ⊂ ·) (𝒜 : Set (Finset α))) (j : Finset.range (n + 1)) : #(𝒜 # j) ≤ 1 := by
  by_contra! ass
  have : (𝒜 # j) ≠ (∅ : Finset (Finset α)) := by
    intro assempty
    have := Finset.card_eq_zero.mpr assempty
    linarith
  obtain ⟨a, amem⟩ := Finset.nonempty_iff_ne_empty.mpr this
  obtain ⟨b, ⟨bmem, aneb⟩⟩ := Finset.exists_mem_ne ass a
  have cardeqab : #a = #b := by rw [(Finset.mem_slice.mp amem).right, (Finset.mem_slice.mp bmem).right]
  exact aneb (IsChain.unique_of_cardinality_chain chain𝒜 (Finset.slice_subset bmem) (Finset.slice_subset amem) cardeqab.symm)

/-- If a chain intersects a layer of the boolean lattice this intersection is a singleton -/
lemma layer_singleton_of_nonempty (chain𝒜 : IsChain (· ⊂ ·) (𝒜 : Set (Finset α))) (j : Finset.range (n + 1)) (layer_nonempty : (𝒜 # j) ≠ ∅):
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

lemma IsChain.ssubset_of_lt_cardinality (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒞) (e₂mem : e₂ ∈ 𝒞)
    (hcard : e₁.card < e₂.card) : e₁ ⊂ e₂ := by
  have e₁nee₂ : e₁ ≠ e₂ := by
    intro ass
    have : e₁.card = e₂.card := by rw [ass]
    linarith
  cases chain𝒞 e₁mem e₂mem e₁nee₂ with
  | inl h => exact Finset.ssubset_iff_subset_ne.mpr ⟨h.left, e₁nee₂⟩
  | inr h =>
    have : e₂.card < e₁.card := Finset.card_strictMono h
    linarith

lemma IsChain.subset_of_le_cardinality (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒞) (e₂mem : e₂ ∈ 𝒞)
    (hcard : e₁.card ≤ e₂.card) : e₁ ⊆ e₂ := by
  cases Nat.eq_or_lt_of_le hcard with
  | inr hcard_lt =>
    exact (IsChain.ssubset_of_lt_cardinality chain𝒞 e₁mem e₂mem hcard_lt).left
  | inl hcard_eq =>
    exact Finset.subset_of_eq (IsChain.unique_of_cardinality_chain chain𝒞 e₁mem e₂mem hcard_eq)



variable [Fintype α] [DecidableEq α] [DecidableEq (Set (Finset α))]

def chain_extension_filter_function (𝒜 : Finset (Finset α)) (e : Finset α) : α → Prop :=
  fun a : α ↦ IsChain (· ⊂ ·) (insert (insert a e) (𝒜 : Set (Finset α))) ∧ insert a e ∉ (𝒜 : Set (Finset α))

instance instDecidablePredChainExtension (e : Finset α) :
    DecidablePred (chain_extension_filter_function 𝒜 e) := by sorry

lemma chain_extension (hn : Fintype.card α = n) {i j : Finset.range (n + 1)} (iltj : i < j) (chain𝒜 : IsChain (· ⊂ ·) (𝒜 : Set (Finset α)))
    (hi : (𝒜 # i) = {layer_i}) (hj : (𝒜 # j) = {layer_j}) (emptylayer : ∀ l ∈ (Finset.range (n + 1)), i < l → l < j → #(𝒜 # l) = 0):
    Finset.filter (chain_extension_filter_function 𝒜 layer_i) (Finset.univ : Finset α) = layer_j \ layer_i := by
  have layer_j_mem : layer_j ∈ 𝒜 := by
        apply (slice_subset : 𝒜 # j ⊆ 𝒜)
        rw [hj]
        exact Finset.mem_singleton.mpr rfl

  have layer_i_mem : layer_i ∈ 𝒜 := by
        apply (slice_subset : 𝒜 # i ⊆ 𝒜)
        rw [hi]
        exact Finset.mem_singleton.mpr rfl

  have layer_i_card : layer_i.card = i := by
    have := Finset.mem_singleton_self layer_i
    simp [←hi, slice] at this
    exact this.right
  have layer_j_card : layer_j.card = j := by
    have := Finset.mem_singleton_self layer_j
    simp [←hj, slice] at this
    exact this.right

  ext x
  let e_new := insert x layer_i
  have he_new : e_new = insert x layer_i := rfl

  have e_new_card_le_layer_j_card: e_new.card ≤ layer_j.card := by

    rw [layer_j_card]
    have : #e_new ≤ #layer_i + 1 := by
      rw [he_new]
      exact Finset.card_insert_le x layer_i
    rw [layer_i_card] at this
    apply Nat.le_trans this
    exact Nat.succ_le_of_lt iltj

  constructor
  · intro hx
    simp [chain_extension_filter_function] at hx

    simp [←he_new] at hx
    have e_new_neq_layer_j : e_new ≠ layer_j := by
      intro ass
      rw [←ass] at layer_j_mem
      exact hx.right layer_j_mem
    simp
    constructor
    · have e_new_mem : e_new ∈ insert e_new (𝒜 : Set (Finset α)) := by simp
      have layer_j_mem_insert : layer_j ∈ insert e_new (𝒜 : Set (Finset α)) := by
        simp
        right
        exact layer_j_mem
      have e_new_sub_layer_j := IsChain.subset_of_le_cardinality hx.left e_new_mem layer_j_mem_insert e_new_card_le_layer_j_card
      rw [he_new] at e_new_sub_layer_j
      exact e_new_sub_layer_j (mem_insert_self x layer_i)
    · intro x_mem_layer_i
      have : e_new = layer_i := Finset.insert_eq_self.mpr x_mem_layer_i
      rw [←this] at layer_i_mem
      exact hx.right layer_i_mem
  · intro hx
    simp at hx
    simp [chain_extension_filter_function]
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
          have := chain𝒜 layer_i_mem e₂_not_new
          by_cases h : layer_i = e₂
          · right
            rw [←h, e₁_new, he_new]
            apply Finset.ssubset_iff_subset_ne.mpr
            constructor
            · simp
            · exact (Finset.insert_ne_self.mpr hx.right).symm
          · cases chain𝒜 e₂_not_new layer_i_mem (fun q => h q.symm) with
            | inl e₂_sub_layer_i =>
              right
              simp at e₂_sub_layer_i
              rw [e₁_new, he_new]
              refine Finset.ssubset_of_ssubset_of_subset e₂_sub_layer_i _
              exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert x layer_i, (Finset.insert_ne_self.mpr hx.right).symm⟩
            | inr layer_i_sub_e₂ =>
              simp at layer_i_sub_e₂
              left
              by_contra e₂_sub_e₁

              have e₁_sub_e₂ : e₁ ⊆ e₂ := by
                rw [e₁_new, he_new]
                have layer_j_card_le_e₂_card : #layer_j ≤ #e₂ := by
                  rw [layer_j_card]
                  by_contra!
                  have e₂_card_gt_i : #e₂ > ↑i := by
                    rw [←layer_i_card]
                    exact Finset.card_strictMono layer_i_sub_e₂
                  have e₂_card_lt_n_succ : #e₂ < n + 1 := by
                    apply Nat.lt_succ_of_le
                    rw [←hn]
                    apply Finset.card_le_univ
                  have e₂_empty_layer := emptylayer #e₂ (by simp; exact e₂_card_lt_n_succ) e₂_card_gt_i this
                  simp at e₂_empty_layer
                  have : e₂ ∈ 𝒜 # #e₂ := by simpa [slice]
                  simp [e₂_empty_layer] at this

                have layer_j_sub_e₂ := IsChain.subset_of_le_cardinality chain𝒜 layer_j_mem e₂_not_new layer_j_card_le_e₂_card

                apply Finset.insert_subset
                · exact layer_j_sub_e₂ hx.left
                · have : #layer_i ≤ #e₂ := by
                    rw [layer_i_card]
                    rw [layer_j_card] at layer_j_card_le_e₂_card
                    exact Nat.le_trans (Nat.le_of_lt iltj) layer_j_card_le_e₂_card

                  exact IsChain.subset_of_le_cardinality chain𝒜 layer_i_mem e₂_not_new this

              have : ¬(e₁ ⊆ e₂ ∧ e₁ ≠ e₂) := fun q => e₂_sub_e₁ (Finset.ssubset_iff_subset_ne.mpr q)
              simp at this
              exact e₁neqe₂ (this e₁_sub_e₂)

      | inr e₁_not_new => sorry
    · --rw [←he_new]
      intro e_new_mem_𝒜
      sorry


lemma one_elt_max_chain_layer (hn : Fintype.card α = n) (maxchain𝒜 : IsMaxChain (· ⊂ ·) (𝒜 : Set (Finset α))) (j : Finset.range (n + 1)) : #(𝒜 # j) = 1 := by
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
    have larger_chain_with_univ : IsChain (· ⊂ ·) ((Insert.insert (Finset.univ : Finset α) 𝒜) : Set (Finset α)) := by
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun h => bneq h.symm⟩

    have univin𝒜 := Set.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_univ (by simp)).symm
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
    have larger_chain_with_empty : IsChain (· ⊂ ·) ((Insert.insert (∅ : Finset α) 𝒜) : Set (Finset α)) := by
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, bneq⟩

    have emptyin𝒜 := Set.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_empty (by simp)).symm
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

    let e_bottom := (layer_singleton_of_nonempty maxchain𝒜.left s_bottom h_s_bottom.right).choose
    have bottom_singleton : 𝒜 # s_bottom = {e_bottom} := (layer_singleton_of_nonempty maxchain𝒜.left s_bottom h_s_bottom.right).choose_spec.left

    let e_top := (layer_singleton_of_nonempty maxchain𝒜.left s_top h_s_top.right).choose
    have top_singleton : 𝒜 # s_top = {e_top} := (layer_singleton_of_nonempty maxchain𝒜.left s_top h_s_top.right).choose_spec.left

    let chain_extension_candidates := Finset.filter (chain_extension_filter_function 𝒜 e_bottom) (Finset.univ : Finset α)

    have chain_extension_candidates_eq : chain_extension_candidates = e_top \ e_bottom :=
      chain_extension hn (Nat.lt_trans h_s_bottom.left h_s_top.left) maxchain𝒜.left bottom_singleton top_singleton emptylayer
    simp at chain_extension_candidates_eq

    have e_bottom_mem_card : e_bottom ∈ 𝒜 ∧ e_bottom.card = s_bottom := by
      have := Finset.mem_singleton_self e_bottom
      rw [←bottom_singleton] at this
      simp [slice] at this
      exact this

    have e_top_mem_card : e_top ∈ 𝒜 ∧ e_top.card = s_top := by
      have := Finset.mem_singleton_self e_top
      rw [←top_singleton] at this
      simp [slice] at this
      exact this

    have chain_extension_candidates_ne_empty : chain_extension_candidates.card > 0 := by
      rw [chain_extension_candidates_eq]
      have card_bottom_lt_card_top : e_bottom.card < e_top.card := by
        rw [e_top_mem_card.right, e_bottom_mem_card.right]
        exact Nat.lt_trans h_s_bottom.left h_s_top.left
      have bottom_subset_top : e_bottom ⊂ e_top :=
        IsChain.ssubset_of_lt_cardinality maxchain𝒜.left e_bottom_mem_card.left e_top_mem_card.left card_bottom_lt_card_top
      have := Finset.card_sdiff_add_card_eq_card bottom_subset_top.left
      linarith
    simp at chain_extension_candidates_ne_empty
    obtain ⟨a, ha⟩ := chain_extension_candidates_ne_empty
    simp [chain_extension_candidates, chain_extension_filter_function] at ha
    have := Set.insert_eq_self.mp (maxchain𝒜.right ha.left (by simp)).symm
    exact ha.right this


lemma card_maxChainThrough {ℬ : Finset (Finset α)} (hn : Fintype.card α = n) (chain : MaxChainThrough ℬ) : #chain.𝒜 = n + 1 := by
  rw [←sum_card_slice chain.𝒜]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(chain.𝒜 # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact one_elt_max_chain_layer hn chain.isMaxChain ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma count_maxChainsThrough {c : ℕ → ℕ} (monc : Monotone c) (hcn : c m = n)
    (ℬ : Finset (Finset α)) (cardℬ : ℬ.card = m) (chainℬ : IsChain (· ⊂ ·) (ℬ : Set (Finset α)))  (cardsℬ : Finset.image Finset.card ℬ = Finset.image c (Finset.range m)) :
      Fintype.card (ℬ.MaxChainThrough) = ∏ j : Fin m, (c (j + 1) - c j)! := by
  induction n - m generalizing n m ℬ with
  | zero => sorry
  | succ s ih => sorry

lemma count_maxChains_through_singleton (e : Finset α) (hn : Fintype.card α = n): Fintype.card (MaxChainThrough {e}) = (#e)! * (n - #e)! := by sorry

/-- The **Lubell-Yamamoto-Meshalkin inequality**. Sperner's Theorem follows as in Mathlib.Combinatorics.SetFamily.LYM as a corollary -/
theorem lym_inequality (antichain𝒜 : IsAntichain (· ⊂ ·) (𝒜 : Set (Finset α))) (hn : Fintype.card α = n):
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

  have slice_partition : Finset.disjiUnion (Iic n) 𝒜.slice (Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)) = (𝒜 : Finset (Finset α)) := by
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
