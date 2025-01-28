import TheBook.ToMathlib.Chain_optional
import TheBook.ToMathlib.List
import Mathlib.Data.Finset.Slice
import Init.Core

namespace Finset

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)} (r : α → α → Prop)
local infixl:50 " ≺ " => r

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

instance card_lt : LT (Finset α) where
  lt x y := #x < #y

instance card_preorder : Preorder (Finset α) := {
  le := (· ≤ ·),
  lt := (· < ·),
  le_refl := fun x =>  Nat.le_refl #x,
  le_trans := fun _ _ _ hxy hyz => Nat.le_trans hxy hyz,
  lt_iff_le_not_le := fun _ _ => Nat.lt_iff_le_not_le
}

instance card_le_is_total : IsTotal 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ≤ e₂.val) :=
  ⟨fun a b ↦ Nat.le_total #a.val #b.val⟩

instance card_le_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ≤ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ ↦ Nat.le_trans h₁ h₂⟩

instance IsChain.card_le_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ⊆ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ => subset_trans h₁ h₂⟩

lemma card_strict_mono' (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : ((Finset.univ : Finset 𝒜).toList.insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val)).Sorted (fun (e₁ e₂ : 𝒜) ↦ #e₁.val < #e₂.val) := by
  apply List.pairwise_iff_get.mpr
  intro x y xlty
  let elt_x := ((List.insertionSort (fun (e₁ e₂ : 𝒜) => #e₁.val ≤ #e₂.val) univ.toList).get x)
  let elt_y := ((List.insertionSort (fun (e₁ e₂ : 𝒜) => #e₁.val ≤ #e₂.val) univ.toList).get y)
  have card_le : elt_x.val ≤ elt_y.val := List.pairwise_iff_get.mp (List.sorted_insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val) (Finset.univ : Finset 𝒜).toList) x y xlty
  by_contra! ass
  have card_eq := Nat.le_antisymm card_le ass

  have elt_x_eq_elt_y := Subtype.eq (IsChain.unique_of_cardinality_chain chain𝒜 elt_x.prop elt_y.prop card_eq)
  have elt_x_neq_elt_y : elt_x ≠ elt_y := List.pairwise_iff_get.mp (List.Nodup.insertionSort ((Finset.univ : Finset 𝒜).nodup_toList)) x y xlty

  exact elt_x_neq_elt_y elt_x_eq_elt_y

lemma Chain.card_strict_mono [DecidableEq α] (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : ∃ l : List (Finset α), l ~ 𝒜.toList ∧ l.Sorted (#· < #·) := by
  let l' := ((Finset.univ : Finset 𝒜).toList.insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val))
  have l'_sorted : l'.Sorted (fun (e₁ e₂ : 𝒜) ↦ #e₁.val < #e₂.val) := card_strict_mono' chain𝒜

  let l := l'.map Subtype.val
  use l
  constructor
  · calc
      l ~ (Finset.univ : Finset 𝒜).toList.map Subtype.val := Perm.map Subtype.val (perm_insertionSort (fun e₁ e₂ => #e₁.val ≤ #e₂.val) (Finset.univ : Finset 𝒜).toList)
      _ ~ 𝒜.toList := by apply Finset.subtype_toList
  · unfold l Sorted
    apply List.pairwise_iff_get.mpr
    intro i j iltj
    simp [List.getElem_map, List.unattach, -List.map_subtype]

    have : (l'.map Subtype.val).length = l'.length := length_map l' Subtype.val

    have iltj_coe : (Fin.cast this i) < (Fin.cast this j) := by
      apply Fin.lt_def.mpr
      simp
      exact iltj

    have := List.pairwise_iff_get.mp l'_sorted (Fin.cast this i) (Fin.cast this j) iltj_coe
    exact this

lemma Chain.layer_singleton_of_nonempty (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (j : Finset.range (n + 1)) (layer_nonempty : (𝒜 # j) ≠ ∅):
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



section ChainExtension

variable {α : Type*} [DecidableEq α] [Fintype α]

def chain_extension_filter_function (𝒜 : Finset (Finset α)) (e : Finset α) : α → Prop :=
  fun a : α ↦ IsChain (· ⊂ ·) (insert (insert a e) 𝒜) ∧ insert a e ∉ 𝒜

variable {𝒜 : Finset (Finset α)}

instance instDecidableIsChain : Decidable (IsChain (· ⊂ ·) 𝒜) := by
  apply Finset.decidableDforallFinset

instance instDecidablePredChainExtension {𝒜 : Finset (Finset α)} (e : Finset α) :
    DecidablePred (chain_extension_filter_function 𝒜 e) :=
  fun a : α => inferInstanceAs (Decidable (IsChain (· ⊂ ·) (insert (insert a e) 𝒜) ∧ insert a e ∉ 𝒜))

def extension_candidates (ℬ : Finset (Finset α)) (e : Finset α) := Finset.filter (chain_extension_filter_function ℬ e) (Finset.univ : Finset α)



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

lemma IsMaxChain.one_elt_max_chain_layer [Fintype α] [DecidableEq α] (hn : Fintype.card α = n) (maxchain𝒜 : IsMaxChain (· ⊂ ·) 𝒜)
    (j : Finset.range (n + 1)) : #(𝒜 # j) = 1 := by
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

    obtain ⟨e_bottom, ⟨bottom_singleton : 𝒜 # s_bottom = {e_bottom}, _⟩⟩ := Chain.layer_singleton_of_nonempty maxchain𝒜.left s_bottom h_s_bottom.right

    obtain ⟨e_top, ⟨top_singleton : 𝒜 # s_top = {e_top}, _⟩⟩ := Chain.layer_singleton_of_nonempty maxchain𝒜.left s_top h_s_top.right

    let extension_candidates := Finset.filter (chain_extension_filter_function 𝒜 e_bottom) (Finset.univ : Finset α)

    have extension_candidates_eq : extension_candidates = e_top \ e_bottom := by
      refine' extension_candidates_characterisation hn _ maxchain𝒜.left bottom_singleton top_singleton emptylayer
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

lemma IsMaxChain.card [Fintype α] [DecidableEq α] {ℬ : Finset (Finset α)} (hn : Fintype.card α = n)
    (maxChainℬ : IsMaxChain (· ⊂ ·) ℬ) : ℬ.card = n + 1 := by
  rw [←sum_card_slice ℬ]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(ℬ # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact IsMaxChain.one_elt_max_chain_layer hn maxChainℬ ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsChain.card_le {ℬ : Finset (Finset α)} [Fintype α] (hn : Fintype.card α = n) (chainℬ : IsChain (· ⊂ ·) ℬ) : ℬ.card ≤ n + 1 := by
  rw [←sum_card_slice ℬ]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(ℬ # r) ≤ ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply sum_le_sum
      intro j jmem
      exact IsChain.max_one_elt_chain_layer chainℬ j
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsMaxChain.iff_card [Fintype α] [DecidableEq α] {ℬ : Finset (Finset α)} (hn : Fintype.card α = n)
    (chainℬ : IsChain (· ⊂ ·) ℬ) : IsMaxChain (· ⊂ ·) ℬ ↔ ℬ.card = n + 1 := by
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
