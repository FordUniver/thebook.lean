import TheBook.ToMathlib.List
import TheBook.ToMathlib.Slice
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Fintype.Basic
import Init.Core

namespace Finset

open Function Finset Nat Set BigOperators List

section ChainSubset

/- Here we proof lemmata concerning the poset of the subset relation on sets of any type-/

variable {α : Type*} {𝒜 : Finset (Finset α)} {ℬ : Finset (Set α)} {𝒞 : Set (Finset α)} {𝒟 : Set (Set α)}

instance : Coe (IsChain (· ⊂ ·) 𝒞) (IsChain (· ⊂ ·) (toSet '' 𝒞)) := ⟨ by
  intro h
  intro x hx y hy x_neg_y
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  have x'_neg_y' : x' ≠ y' := by
    by_contra ass
    rw [ass] at hx'
    rw [←hx'.right, hy'.right] at x_neg_y
    simp at x_neg_y

  simp [←hx'.right, ←hy'.right]
  exact h hx'.left hy'.left x'_neg_y'
⟩

instance : Coe (IsChain (· ⊂ ·) (toSet '' 𝒞)) (IsChain (· ⊂ ·) 𝒞) :=
  ⟨ fun h _ hx _ hy x_neg_y ↦ h (Set.mem_image_of_mem toSet hx) (Set.mem_image_of_mem toSet hy) (fun ass ↦ x_neg_y (coe_inj.mp ass))⟩

instance : Coe (IsChain (· ⊆ ·) (toSet '' 𝒞)) (IsChain (· ⊆ ·) 𝒞) :=
  ⟨ fun h _ hx _ hy x_neg_y ↦ h (Set.mem_image_of_mem toSet hx) (Set.mem_image_of_mem toSet hy) (fun ass ↦ x_neg_y (coe_inj.mp ass))⟩

instance : Coe (IsChain (· ⊂ ·) (toSet '' 𝒞)) (IsChain (· ⊂ ·) 𝒞) := ⟨ by
  intro h
  intro x hx y hy x_neg_y
  exact h (Set.mem_image_of_mem toSet hx) (Set.mem_image_of_mem toSet hy) (fun ass ↦ x_neg_y (coe_inj.mp ass))
⟩

instance [Fintype 𝒞] : Coe (IsChain (· ⊂ ·) 𝒞) (IsChain (· ⊂ ·) 𝒞.toFinset.toSet) := ⟨ by
  intro h x hx Real.young_inequality hy x_neg_y
  simp at hx hy
  exact h hx hy x_neg_y
⟩

lemma IsChain.equivalence_subset_relations : (IsChain (· ⊆ .) 𝒟) ↔ (IsChain (· ⊂ .) 𝒟) := by
  constructor
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ => left; exact Set.ssubset_iff_subset_ne.mpr ⟨e₁sube₂, e₁neqe₂⟩
    | inr e₂sube₁ => right; exact Set.ssubset_iff_subset_ne.mpr ⟨e₂sube₁, e₁neqe₂.symm⟩
  · intro h e₁ e₁mem e₂ e₂mem e₁neqe₂
    cases h e₁mem e₂mem e₁neqe₂ with
    | inl e₁sube₂ => left; exact e₁sube₂.left
    | inr e₂sube₁ => right; exact e₂sube₁.left

example (h : IsChain (· ⊂ ·) 𝒞) : (IsChain (· ⊆ ·) (toSet '' 𝒞)) := IsChain.equivalence_subset_relations.mpr h

example (h : IsChain (· ⊂ ·) 𝒞) : (IsChain (· ⊆ ·) 𝒞) := (IsChain.equivalence_subset_relations.mpr h : IsChain (· ⊆ ·) (toSet '' 𝒞))

lemma IsMaxChain.equivalence_subset_relations : (IsMaxChain (· ⊆ .) 𝒟) ↔ (IsMaxChain (· ⊂ .) 𝒟) := by
  constructor
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mp h.left, fun t chain => h.right (IsChain.equivalence_subset_relations.mpr chain)⟩
  · intro h
    exact ⟨IsChain.equivalence_subset_relations.mpr h.left, fun t chain => h.right (IsChain.equivalence_subset_relations.mp chain)⟩

lemma IsChain.unique_of_cardinality_chain (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {a b : Finset α}
    (amem : a ∈ 𝒞) (bmem : b ∈ 𝒞) (hcard : #a = #b) : a = b := by
  by_contra aneb
  cases chain𝒞 amem bmem aneb with
  | inl h =>
    have := Finset.card_strictMono h
    linarith
  | inr h =>
    have := Finset.card_strictMono h
    linarith

lemma IsChain.max_one_elt_chain_layer [Fintype 𝒞] (chain𝒞 : IsChain (· ⊂ ·) 𝒞) (j : ℕ) : #(𝒞.toFinset # j) ≤ 1 := by
  by_contra! ass
  have : (𝒞.toFinset # j) ≠ (∅ : Finset (Finset α)) := by
    intro assempty
    have := Finset.card_eq_zero.mpr assempty
    linarith
  obtain ⟨a, amem⟩ := Finset.nonempty_iff_ne_empty.mpr this
  obtain ⟨b, ⟨bmem, aneb⟩⟩ := Finset.exists_mem_ne ass a
  have cardeqab : #a = #b := by rw [(Finset.mem_slice.mp amem).right, (Finset.mem_slice.mp bmem).right]
  have := Finset.slice_subset (bmem)
  exact aneb (IsChain.unique_of_cardinality_chain chain𝒞 (mem_toFinset.mp (Finset.slice_subset bmem)) (mem_toFinset.mp (Finset.slice_subset amem)) cardeqab.symm)

instance IsChain.subset_is_trans : IsTrans 𝒜 (fun (e₁ e₂ : 𝒜) ↦ e₁.val ⊆ e₂.val) :=
  ⟨fun _ _ _ h₁ h₂ => subset_trans h₁ h₂⟩

lemma Chain.layer_singleton_of_nonempty [Fintype 𝒞] (chain𝒞 : IsChain (· ⊂ ·) 𝒞) (j : Finset.range (n + 1)) (layer_nonempty : (𝒞.toFinset # j) ≠ ∅):
    ∃! e : Finset α, 𝒞.toFinset # j = {e} := by
  have : # (𝒞.toFinset # j) = 1 := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer chain𝒞 j) with
    | inl card_zero =>
      simp at card_zero
      exact False.elim (layer_nonempty card_zero)
    | inr card_one => exact card_one
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp this
  have unique : ∀ a : Finset α, 𝒞.toFinset # j = {a} → a = e := by
    intro a ha
    rw [he] at ha
    simp at ha
    exact ha.symm

  exact ⟨e, he, unique⟩

lemma IsChain.ssubset_of_lt_cardinality (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒞) (e₂mem : e₂ ∈ 𝒞)
    (hcard : #e₁ < #e₂) : e₁ ⊂ e₂ := by
  have e₁nee₂ : e₁ ≠ e₂ := by
    intro ass
    have : #e₁ = #e₂ := by rw [ass]
    linarith
  cases chain𝒞 e₁mem e₂mem e₁nee₂ with
  | inl h => exact Finset.ssubset_iff_subset_ne.mpr ⟨h.left, e₁nee₂⟩
  | inr h =>
    have : #e₂ < #e₁ := Finset.card_strictMono h
    linarith

lemma IsChain.subset_of_le_cardinality (chain𝒞 : IsChain (· ⊂ ·) 𝒞) {e₁ e₂ : Finset α} (e₁mem : e₁ ∈ 𝒞) (e₂mem : e₂ ∈ 𝒞)
    (hcard : #e₁ ≤ #e₂) : e₁ ⊆ e₂ := by
  cases Nat.eq_or_lt_of_le hcard with
  | inr hcard_lt =>
    exact (IsChain.ssubset_of_lt_cardinality chain𝒞 e₁mem e₂mem hcard_lt).left
  | inl hcard_eq =>
    exact Finset.subset_of_eq (IsChain.unique_of_cardinality_chain chain𝒞 e₁mem e₂mem hcard_eq)

end ChainSubset


section ChainExtension

variable {α : Type*} [DecidableEq α] [Fintype α] {𝒜 : Set (Finset α)} [DecidablePred (· ∈ 𝒜)]
instance : Fintype 𝒜 := setFintype 𝒜

def chain_extension_filter_function (ℬ : Set (Finset α)) (e : Finset α) : α → Prop :=
  fun a : α ↦ IsChain (· ⊂ ·) (insert (insert a e) ℬ) ∧ insert a e ∉ ℬ

instance instDecidableIsChain : Decidable (IsChain (· ⊂ ·) 𝒜) := by
  sorry --apply Finset.decidableDforallFinset

instance instDecidablePredChainExtension (e : Finset α) :
    DecidablePred (chain_extension_filter_function 𝒜 e) :=
  fun a : α => by sorry --inferInstanceAs (Decidable (IsChain (· ⊂ ·) (insert (insert a e) 𝒜).toSet ∧ insert a e ∉ 𝒜))

def extension_candidates (ℬ : Set (Finset α)) (e : Finset α) := Finset.filter (chain_extension_filter_function ℬ e) (Finset.univ : Finset α)

theorem extension_candidates_characterisation {i j : Finset.range (n + 1)} (hn : Fintype.card α = n) (ilej_succ_succ : (i : ℕ) + 2 ≤ (j : ℕ)) (chain𝒜 : IsChain (· ⊂ ·) 𝒜)
    (hi : (𝒜.toFinset # i) = {layer_i}) (hj : (𝒜.toFinset # j) = {layer_j}) (emptylayer : ∀ l ∈ (Finset.range (n + 1)), i < l → l < j → #(𝒜.toFinset # l) = 0):
    extension_candidates 𝒜 layer_i = layer_j \ layer_i := by
  unfold extension_candidates

  have layer_j_mem_card := Slice.singleton_explicit.mp hj
  have layer_i_mem_card := Slice.singleton_explicit.mp hi

  ext x
  let e_new := insert x layer_i
  have he_new : e_new = insert x layer_i := rfl

  have e_new_card_lt_layer_j_card: #e_new < #layer_j := by
    rw [layer_j_mem_card.right.left]
    have : #e_new ≤ #layer_i + 1 := by
      simp only [e_new]
      exact Finset.card_insert_le x layer_i
    rw [layer_i_mem_card.right.left] at this
    apply Nat.lt_of_le_of_lt this
    exact Nat.succ_le_of_lt ilej_succ_succ

  constructor
  · intro hx
    simp only [mem_filter, chain_extension_filter_function, ←he_new] at hx
    have hx := hx.right

    have e_new_neq_layer_j : e_new ≠ layer_j := by
      intro ass
      have := mem_toFinset.mp layer_j_mem_card.left
      rw [←ass] at this
      exact hx.right this
    simp
    constructor
    · have e_new_mem : e_new ∈ insert e_new 𝒜 := by simp
      have layer_j_mem_insert : layer_j ∈ insert e_new 𝒜 := by
        simp
        right
        exact Set.mem_toFinset.mp (layer_j_mem_card.left)
      have e_new_sub_layer_j := IsChain.subset_of_le_cardinality hx.left e_new_mem (layer_j_mem_insert) (Nat.le_of_lt e_new_card_lt_layer_j_card)
      rw [he_new] at e_new_sub_layer_j
      exact e_new_sub_layer_j (mem_insert_self x layer_i)
    · intro x_mem_layer_i
      have := mem_toFinset.mp layer_i_mem_card.left
      rw [←(Finset.insert_eq_self.mpr x_mem_layer_i)] at this
      exact hx.right this
  · intro hx
    simp at hx
    simp [chain_extension_filter_function]

    have case_helper {e₁ e₂ : Finset α} (e₁neqe₂ : e₁ ≠ e₂) (e₂_not_new : e₂ ∈ 𝒜) (e₁_new : e₁ = e_new) : e₁ ⊂ e₂ ∨ e₂ ⊂ e₁ := by
      have := chain𝒜 (mem_toFinset.mp layer_i_mem_card.left) e₂_not_new
      by_cases h : layer_i = e₂
      · right
        rw [←h, e₁_new, he_new]
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · simp
        · exact (Finset.insert_ne_self.mpr hx.right).symm
      · cases chain𝒜 e₂_not_new (mem_toFinset.mp layer_i_mem_card.left) (fun q => h q.symm) with
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
              rw [layer_j_mem_card.right.left]
              by_contra!
              have e₂_card_gt_i : #e₂ > ↑i := by
                rw [←layer_i_mem_card.right.left]
                exact Finset.card_strictMono layer_i_sub_e₂
              have e₂_card_lt_n_succ : #e₂ < n + 1 := by
                apply Nat.lt_succ_of_le
                rw [←hn]
                apply Finset.card_le_univ
              have e₂_empty_layer := emptylayer #e₂ (by simp; exact e₂_card_lt_n_succ) e₂_card_gt_i this
              simp at e₂_empty_layer
              have : e₂ ∈ 𝒜.toFinset # #e₂ := by simpa [slice]
              simp [e₂_empty_layer] at this

            have layer_j_sub_e₂ := IsChain.subset_of_le_cardinality chain𝒜 (mem_toFinset.mp layer_j_mem_card.left) e₂_not_new layer_j_card_le_e₂_card

            apply Finset.insert_subset
            · exact layer_j_sub_e₂ hx.left
            · have : #layer_i ≤ #e₂ := by
                rw [layer_i_mem_card.right.left]
                rw [layer_j_mem_card.right.left] at layer_j_card_le_e₂_card
                exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_succ_lt ilej_succ_succ)) layer_j_card_le_e₂_card

              exact IsChain.subset_of_le_cardinality chain𝒜 (mem_toFinset.mp layer_i_mem_card.left) e₂_not_new this

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
      have e_new_card_gt_layer_i : #e_new > i := by simp [Finset.card_insert_of_not_mem hx.right, layer_i_mem_card.right.left]

      rw [layer_j_mem_card.right.left] at e_new_card_lt_layer_j_card
      have : #(𝒜.toFinset # #e_new) = 0 := by
        refine' emptylayer #e_new _ e_new_card_gt_layer_i e_new_card_lt_layer_j_card
        · simp
          exact Nat.lt_trans e_new_card_lt_layer_j_card (mem_range.mp j.property)
      have : (𝒜.toFinset # #e_new).Nonempty := by
        have : e_new ∈ 𝒜.toFinset # #e_new := by simpa [slice]
        exact nonempty_of_mem this
      have : #(𝒜.toFinset # #e_new) > 0 := Finset.card_pos.mpr this
      linarith

lemma extension_candidates_nonempty {e : Finset α} (hn : Fintype.card α = n) (h : extension_candidates 𝒜 e ≠ ∅) : #e < n ∧ (𝒜.toFinset # (#e + 1)) = ∅ := by
  by_contra! ass₀
  apply h
  have : (𝒜.toFinset # (#e + 1)) ≠ ∅ ∨ #e ≥ n := by
    by_cases h : #e < n
    · exact Or.inl (ass₀ h)
    · exact Or.inr (Nat.ge_of_not_lt h)

  cases this with
  | inl next_ne_empty =>
    by_contra! ass₁
    obtain ⟨a, ha⟩ := nonempty_of_ne_empty ass₁
    simp [extension_candidates, chain_extension_filter_function] at ha

    obtain ⟨u, hu⟩ := nonempty_of_ne_empty next_ne_empty
    simp [slice] at hu

    have insert_a_mem : (insert a e) ∈ insert (insert a e) 𝒜 := Set.mem_insert (insert a e) 𝒜
    have u_mem : u ∈ insert (insert a e) 𝒜 := Set.mem_insert_of_mem (insert a e) hu.left

    have card_eq : #(insert a e) = #u := by sorry

    have := IsChain.unique_of_cardinality_chain ha.left insert_a_mem u_mem card_eq
    rw [this] at ha
    exact ha.right hu.left
  | inr card_ge =>
    sorry

end ChainExtension

section ChainSubsetFintype

/- Here we proof lemmata concerning the poset of the subset relation on sets of finite type-/

variable {α : Type*} [Fintype α] {𝒜 : Set (Finset α)} [DecidablePred (· ∈ 𝒜)]

instance : Fintype 𝒜 := setFintype 𝒜

lemma Chain.empty_layer_by_card (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (card𝒜 : #𝒜.toFinset < n+1) : ∃ i : Fin (n + 1), #(𝒜.toFinset # i) = 0 := by
  by_contra! ass
  have : ∀ (i : Fin (n + 1)), #(𝒜.toFinset # i) = 1 := by
    intro i
    have non_zero := ass i
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer chain𝒜 i) with
    | inl h => exfalso; exact (non_zero h)
    | inr h => exact h
  rw [←sum_card_slice 𝒜.toFinset] at card𝒜
  have := calc
    ∑ r ∈ Iic (Fintype.card α), #(𝒜.toFinset # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact this ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]
  linarith

lemma IsMaxChain.one_elt_max_chain_layer [DecidableEq α] (hn : Fintype.card α = n) (maxchain𝒜 : IsMaxChain (· ⊂ ·) 𝒜)
    (j : Finset.range (n + 1)) : #(𝒜.toFinset # j) = 1 := by
  by_contra! ass
  have empty_layer : 𝒜.toFinset # j = ∅ := by
    cases Nat.le_one_iff_eq_zero_or_eq_one.mp (IsChain.max_one_elt_chain_layer maxchain𝒜.left j) with
    | inl h => simp at h; exact h
    | inr h => omega

  if htop : ∀ i : Finset.range (n + 1), i > j → 𝒜.toFinset # i = ∅ then
    have univnotin𝒜 : (Finset.univ : Finset α) ∉ 𝒜 := by
      intro ass₂
      have nslicemem : (Finset.univ : Finset α) ∈ 𝒜.toFinset # n := by
        simp [Finset.slice]
        exact ⟨ass₂, hn⟩
      cases Nat.lt_or_ge j n with
      | inl jltn =>
        have nsliceempty : 𝒜.toFinset # n = ∅ := htop ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n)⟩ jltn
        simp [nsliceempty] at nslicemem
      | inr jgen =>
        have jeqn : j = n := Nat.eq_of_le_of_lt_succ jgen (Finset.mem_range.1 (by simp))
        rw [jeqn] at empty_layer
        simp [empty_layer] at nslicemem
    simp [IsMaxChain] at maxchain𝒜

    have larger_chain_with_univ' : _root_.IsChain (· ⊂ ·) (Insert.insert (Finset.univ : Finset α) 𝒜) := by
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      right
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, fun h => bneq h.symm⟩

    have larger_chain_with_univ : IsChain (· ⊂ ·) ((Insert.insert (Finset.univ : Finset α) 𝒜)) := larger_chain_with_univ'

    have univin𝒜 := Set.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_univ (by simp)).symm
    exact univnotin𝒜 univin𝒜
  else if hbottom : ∀ i : Finset.range (n + 1), i < j → 𝒜.toFinset # i = ∅ then
    have emptynotin𝒜 : (∅ : Finset α) ∉ 𝒜 := by
      intro ass₃
      have zeroslicemem : (∅ : Finset α) ∈ 𝒜.toFinset # 0 := by
        simp [Finset.slice]
        exact ass₃
      cases Nat.eq_zero_or_pos j with
      | inl jeqzero =>
        rw [jeqzero] at empty_layer
        simp [empty_layer] at zeroslicemem
      | inr jgen =>
        simp [hbottom ⟨0, by simp⟩ jgen] at zeroslicemem
    simp [IsMaxChain] at maxchain𝒜
    have larger_chain_with_empty' : _root_.IsChain (· ⊂ ·) (Insert.insert (∅ : Finset α) 𝒜) := by
      have : (Insert.insert (∅ : Finset α) 𝒜) = Insert.insert (∅ : Finset α) 𝒜 := by simp
      rw [this]
      refine' IsChain.insert maxchain𝒜.left  _
      intro b bmem bneq
      left
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, bneq⟩

    have larger_chain_with_empty : IsChain (· ⊂ ·) (Insert.insert (∅ : Finset α) 𝒜) := larger_chain_with_empty'

    have emptyin𝒜 := Set.insert_eq_self.mp (maxchain𝒜.right larger_chain_with_empty (by simp)).symm
    exact emptynotin𝒜 emptyin𝒜

  else
    simp at htop hbottom
    let indices_nonempty_top := Finset.filter (fun i : Finset.range (n + 1) ↦ i > j ∧ 𝒜.toFinset # i ≠ ∅) (Finset.univ : Finset (Finset.range (n + 1)))
    let indices_nonempty_bottom := Finset.filter (fun i : Finset.range (n + 1) ↦ i < j ∧ 𝒜.toFinset # i ≠ ∅) (Finset.univ : Finset (Finset.range (n + 1)))
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

    have emptylayer : ∀ l ∈ (Finset.range (n + 1)), s_bottom < l → l < s_top → #(𝒜.toFinset # l) = 0 := by
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

    obtain ⟨e_bottom, ⟨bottom_singleton : 𝒜.toFinset # s_bottom = {e_bottom}, _⟩⟩ := Chain.layer_singleton_of_nonempty maxchain𝒜.left s_bottom h_s_bottom.right

    obtain ⟨e_top, ⟨top_singleton : 𝒜.toFinset # s_top = {e_top}, _⟩⟩ := Chain.layer_singleton_of_nonempty maxchain𝒜.left s_top h_s_top.right

    have extension_candidates_eq : extension_candidates 𝒜 e_bottom = e_top \ e_bottom := by
      have ilej_succ_succ : (s_bottom : ℕ) + 2 ≤ (s_top : ℕ) := by
        apply Nat.succ_le_of_lt
        have : (s_bottom : ℕ) + 1 ≤ ↑j := Nat.succ_le_of_lt h_s_bottom.left
        exact Nat.lt_of_le_of_lt this h_s_top.left
      exact extension_candidates_characterisation hn ilej_succ_succ maxchain𝒜.left bottom_singleton top_singleton emptylayer

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

    have extension_candidates_ne_empty : #(extension_candidates 𝒜 e_bottom) > 0 := by
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
    have := Set.insert_eq_self.mp (maxchain𝒜.right ha.left (by simp)).symm
    exact ha.right this

lemma IsMaxChain.card [DecidableEq α] (hn : Fintype.card α = n)
    (maxChain𝒜 : IsMaxChain (· ⊂ ·) 𝒜) : #𝒜.toFinset = n + 1 := by
  rw [←sum_card_slice 𝒜.toFinset]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(𝒜.toFinset # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply Finset.sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact IsMaxChain.one_elt_max_chain_layer hn maxChain𝒜 ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsChain.card_le (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : #𝒜.toFinset ≤ n + 1 := by
  rw [←sum_card_slice 𝒜.toFinset]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(𝒜.toFinset # r) ≤ ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply sum_le_sum
      intro j jmem
      exact IsChain.max_one_elt_chain_layer chain𝒜 j
    _ = n + 1 := by rw [←(Finset.card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma IsMaxChain.iff_card [DecidableEq α] (hn : Fintype.card α = n)
    (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : IsMaxChain (· ⊂ ·) 𝒜 ↔ #𝒜.toFinset = n + 1 := by
  constructor
  · intro maxChain𝒜
    exact IsMaxChain.card hn maxChain𝒜
  · intro card𝒜
    constructor
    · exact chain𝒜
    · intro ℬ chainℬ 𝒜ssubℬ
      have : DecidablePred (fun e : Finset α ↦ e ∈ ℬ) := by sorry
      have := setFintype ℬ
      have hcard𝒜 : #ℬ.toFinset ≤ #𝒜.toFinset := by
        rw [card𝒜, ←hn]
        sorry
      exact toFinset_inj.mp ((Finset.subset_iff_eq_of_card_le hcard𝒜).mp (toFinset_subset_toFinset.mpr 𝒜ssubℬ))

end ChainSubsetFintype

section ChainCardinalityOrder

/-
  Given a finite chain of finite sets with respect to the subset relation, we consider the list of chain elements.
  Here we proof that if this list is sorted with respect to the cardinalities it is actually sorted in a strictly monotone manner.
-/

variable {α : Type*} {𝒜 : Set (Finset α)} [DecidablePred (· ∈ 𝒜)] [Fintype α]

instance : Fintype 𝒜 := setFintype 𝒜

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

theorem Chain.card_strict_mono [DecidableEq α] (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : ∃ l : List (Finset α), l ~ 𝒜.toFinset.toList ∧ l.Sorted (#· < #·) := by
  let l' := ((Finset.univ : Finset 𝒜).toList.insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val))
  have l'_sorted : l'.Sorted (fun (e₁ e₂ : 𝒜) ↦ #e₁.val < #e₂.val) := card_strict_mono' chain𝒜

  let l := l'.map Subtype.val
  use l
  constructor
  · calc
      l ~ (Finset.univ : Finset 𝒜).toList.map Subtype.val := Perm.map Subtype.val (perm_insertionSort (fun e₁ e₂ => #e₁.val ≤ #e₂.val) (Finset.univ : Finset 𝒜).toList)
      _ ~ 𝒜.toFinset.toList := by apply Finset.subtype_toList
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

end ChainCardinalityOrder
