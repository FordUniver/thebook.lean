import TheBook.ToMathlib.Chain
import TheBook.ToMathlib.List

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} {𝒜 ℬ : Set (Finset α)}

set_option maxHeartbeats 500000

namespace Finset

section MaxChainThrough

/-
  In this section we define the maximal chains with respect to the subset relation that extend a given chain.
  Further in the finite case we give an explicit formula for the number of such maximal extensions.
-/

structure MaxChainThrough (ℬ : Set (Finset α)) where
  𝒜 : Set (Finset α)
  isMaxChain : IsMaxChain (· ⊂ ·) 𝒜
  subChain : ℬ ⊆ 𝒜

def emb_MaxChainThrough (ℬ : Set (Finset α)) (X : MaxChainThrough ℬ) : Set (Finset α) := X.𝒜

@[ext] lemma MaxChainThrough_eq (𝒞₁ 𝒞₂ : MaxChainThrough ℬ) (hA : 𝒞₁.𝒜 = 𝒞₂.𝒜) : 𝒞₁ = 𝒞₂ := by
  cases 𝒞₁
  cases 𝒞₂
  congr

lemma inj_emb_MaxChainThrough : Injective (emb_MaxChainThrough ℬ) := by
  intro 𝒞₁ 𝒞₂ h
  unfold emb_MaxChainThrough at h
  ext
  rw [h]

instance instFintypeMaxChainThrough : Fintype (MaxChainThrough ℬ) := by sorry

variable [Fintype α] [DecidableEq α] [DecidableEq (Set (Finset α))]

instance {C : MaxChainThrough ℬ} : DecidablePred (· ∈ C.𝒜) := by sorry
instance : DecidablePred (· ∈ ℬ) := by sorry
instance : DecidablePred (· ∈ 𝒜) := by sorry

instance {C : MaxChainThrough ℬ} : Fintype C.𝒜 := setFintype C.𝒜

instance : Fintype ℬ := setFintype ℬ
instance : Fintype 𝒜 := setFintype 𝒜

lemma card_maxChainThrough (hn : Fintype.card α = n) (chain : MaxChainThrough ℬ) : #chain.𝒜.toFinset = n + 1 := by
  rw [←sum_card_slice chain.𝒜.toFinset]
  calc
    ∑ r ∈ Iic (Fintype.card α), #(chain.𝒜.toFinset # r) = ∑ r ∈ Iic (Fintype.card α), 1 := by
      apply sum_congr (by rfl)
      intro j jmem
      simp [hn] at jmem
      exact IsMaxChain.one_elt_max_chain_layer hn chain.isMaxChain ⟨j, by simp [Nat.lt_succ_of_le jmem]⟩
    _ = n + 1 := by rw [←(card_eq_sum_ones (Iic (Fintype.card α)))]; simp [hn]

lemma first_entry (list : List (Finset α))
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toFinset.toList ~ list)
    (empty_in_chain : ∅ ∈ ℬ) : list[0]'(by rw [←Perm.length_eq h_list]; exact length_pos_of_mem (mem_toList.mpr (mem_toFinset.mpr empty_in_chain))) = ∅ := by sorry

lemma last_entry {list : List (Finset α)}
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toFinset.toList ~ list)
    (univ_in_chain : univ ∈ ℬ) : list[list.length - 1]'(by sorry) = univ := by sorry

lemma incident_indices_monotone_cards {s t : Fin (n + 1)} {ℬ : Finset (Finset α)} (ilej_succ_succ : s.val + 2 ≤ t.val) (list : List (Finset α))
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toList ~ list)
    (hs : (ℬ # s) = {layer_s}) (ht : (ℬ # t) = {layer_t})
    (empty_layer : ∀ j : Fin (n + 1), s < j → j < t → #(ℬ # ↑j) = 0) :
    ∃ i_s : Fin (list.length - 1), list[i_s.val]  = layer_s ∧ list[i_s.val + 1] = layer_t := by

  let i_s := list.indexOf layer_s
  have i_s_in_range : i_s < list.length := List.indexOf_lt_length.mpr (h_list.subset (mem_toList.mpr (Slice.singleton_explicit.mp hs).left))
  have h_i_s : list[i_s] = layer_s := list.indexOf_get i_s_in_range

  let i_t := list.indexOf layer_t
  have i_t_in_range : i_t < list.length := List.indexOf_lt_length.mpr (h_list.subset (mem_toList.mpr (Slice.singleton_explicit.mp ht).left))
  have h_i_t : list[i_t] = layer_t := list.indexOf_get i_t_in_range

  simp at i_t_in_range
  simp at i_s_in_range

  have i_s_eq_i_t_succ : i_t = i_s + 1 := by
    by_contra ass₁
    have : i_t > i_s := by
      by_contra! ass₂
      unfold List.Sorted at monotone_cards
      have : list[i_t] ≤ list[i_s] := by
        cases le_iff_eq_or_lt.mp ass₂ with
        | inl h =>
          simp [h]
        | inr h =>
          have : i_t < list.length := by
            simpa
          have := ((List.pairwise_iff_get.mp monotone_cards) ⟨i_t, by simpa⟩ ⟨i_s, by simpa⟩ h)
          simp at this
          exact le_of_lt this
      simp [h_i_s, h_i_t] at this
      have : t.val ≤ s.val := by
        simp [←(Slice.singleton_explicit.mp hs).right.left, ←(Slice.singleton_explicit.mp ht).right.left]
        exact this
      linarith
    have i_s_succ_lt : i_s + 1 < i_t := Nat.lt_of_le_of_ne this fun a => ass₁ (id (Eq.symm a))

    let e := list[i_s + 1]

    have e_card_gt' : #e > s := by
      have := (List.pairwise_iff_get.mp monotone_cards) ⟨i_s, by simpa⟩ ⟨i_s + 1, by apply Nat.lt_trans i_s_succ_lt; simpa ⟩ (by simp : i_s < i_s + 1)
      simp [h_i_s, (Slice.singleton_explicit.mp hs).right.left] at this
      unfold e
      exact this

    have e_card_lt' : #e < t := by
      have := (List.pairwise_iff_get.mp monotone_cards) ⟨i_s + 1, by apply Nat.lt_trans i_s_succ_lt; simpa⟩ ⟨i_t, by simpa⟩ i_s_succ_lt
      simp [h_i_t, (Slice.singleton_explicit.mp ht).right.left] at this
      exact this

    have card_e_mod : #e % (n + 1) = #e := mod_eq_of_lt (Nat.lt_trans e_card_lt' t.is_lt)

    have e_card_gt : Fin.ofNat #e > s := by simp [Fin.ofNat, card_e_mod]; exact e_card_gt'
    have e_card_lt : Fin.ofNat #e < t := by simp [Fin.ofNat, card_e_mod]; exact e_card_lt'

    have layer_empty := empty_layer (Fin.ofNat #e) e_card_gt e_card_lt

    have layer_nonempty : e ∈ (ℬ # ↑(Fin.ofNat #e : Fin (n + 1))) := by
      simp [mem_slice]
      constructor
      · apply mem_toList.mp
        exact (List.Perm.symm h_list).subset ((List.get_mem list (i_s + 1)) (Nat.lt_trans i_s_succ_lt i_t_in_range))
      · simp [Fin.ofNat, card_e_mod]

    simp at layer_empty

    simp [layer_empty] at layer_nonempty

  have i_s_upperbound : i_s < list.length - 1 :=
    have : i_s + 1 < list.length := by rw [←i_s_eq_i_t_succ]; exact i_t_in_range
    lt_sub_of_add_lt this

  use ⟨i_s, i_s_upperbound⟩

  simp only [i_s_eq_i_t_succ] at h_i_t
  exact ⟨h_i_s, h_i_t⟩

def extensions_wrt [DecidableEq (Set (Finset α))] [DecidableEq (Finset α)] (ℬ : Set (Finset α)) (e : Finset α) (x : α) : Finset (Set (Finset α)) := by
  let ℬ' := Insert.insert (Insert.insert x e) ℬ
  let e := (emb_MaxChainThrough ℬ')
  exact (univ : Finset (MaxChainThrough ℬ')).image (emb_MaxChainThrough ℬ')

variable [DecidableEq (Set (Finset α))] [DecidableEq (Finset α)]

lemma chain_through_extension_candidates_pairwiseDisjoint {e : Finset α} (e_mem : e ∈ ℬ) : PairwiseDisjoint (extension_candidates ℬ e) (extensions_wrt ℬ e) := by
  intro x hx y hy xneqy
  simp [_root_.Disjoint]
  simp [extensions_wrt]
  intro A hA_x hA_y
  intro 𝒜 h𝒜
  simp

  simp [extension_candidates,chain_extension_filter_function] at hx hy

  have a_extension_e_x := hA_x h𝒜
  have a_extension_e_y := hA_y h𝒜
  simp at a_extension_e_x a_extension_e_y

  obtain ⟨𝒜_x, image_𝒜_x⟩ := a_extension_e_x
  obtain ⟨𝒜_y, image_𝒜_y⟩ := a_extension_e_y

  unfold emb_MaxChainThrough at image_𝒜_x image_𝒜_y

  have x_e_mem_𝒜_y : (insert x e) ∈ 𝒜_y.𝒜 := by
    rw [image_𝒜_y, ←image_𝒜_x]
    apply 𝒜_x.subChain
    simp

  have y_e_mem_𝒜_y : (insert y e) ∈ 𝒜_y.𝒜 := by apply 𝒜_y.subChain; simp

  have x_nmem : x ∉ e := by
    by_contra! ass
    rw [insert_eq_of_mem ass] at hx
    exact hx.right e_mem

  have y_nmem : y ∉ e := by
    by_contra! ass
    rw [insert_eq_of_mem ass] at hy
    exact hy.right e_mem

  have eq_card : #(insert x e) = #(insert y e) := by
    rw [Finset.card_insert_of_not_mem x_nmem, Finset.card_insert_of_not_mem y_nmem]

  have : y = x ∨ y ∈ e := by
    apply mem_insert.mp
    rw [IsChain.unique_of_cardinality_chain 𝒜_y.isMaxChain.left x_e_mem_𝒜_y y_e_mem_𝒜_y eq_card]
    exact mem_insert_self y e

  cases this with
  | inl h => exact xneqy h.symm
  | inr h => exact y_nmem h

lemma central_identity (e : Finset α) (e_mem : e ∈ ℬ) (h : extension_candidates ℬ e ≠ ∅):
    (univ : Finset (MaxChainThrough ℬ)).image (emb_MaxChainThrough ℬ) = (extension_candidates ℬ e).disjiUnion (extensions_wrt ℬ e)
    (chain_through_extension_candidates_pairwiseDisjoint e_mem) := by
  ext
  constructor
  · intro 𝒜_mem_image
    simp at 𝒜_mem_image

    simp [extension_candidates, chain_extension_filter_function, extensions_wrt]

    have e_card_lt := (extension_candidates_nonempty rfl h).left

    obtain ⟨C,C_emb⟩ := 𝒜_mem_image
    simp [emb_MaxChainThrough] at C_emb

    have card_next := IsMaxChain.one_elt_max_chain_layer rfl C.isMaxChain ⟨#e + 1, mem_range.mpr ((add_lt_add_iff_right 1).mpr e_card_lt)⟩
    obtain ⟨u, hu⟩ := card_eq_one.mp card_next

    have u_slice := mem_singleton_self u
    rw [←hu] at u_slice
    simp [slice] at u_slice

    have card_e_lt_u : #e < #u := by sorry

    have e_ssub_u := IsChain.ssubset_of_lt_cardinality C.isMaxChain.left (C.subChain e_mem) u_slice.left card_e_lt_u

    obtain ⟨a, ha⟩ := sdiff_nonempty.mpr (not_subset_of_ssubset e_ssub_u)

    use a

    constructor
    · sorry
    · sorry
  · sorry

lemma range_empty_layer (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (empty_layer : ∃ i : Fin (n + 1), #(𝒜.toFinset # i) = 0) (empty_elt : ∅ ∈ 𝒜) (univ_elt : univ ∈ 𝒜) :
    ∃ s : Fin (n + 1), ∃ t : Fin (n + 1), s.val + 2 ≤ t.val ∧ #(𝒜.toFinset # s) = 1 ∧ #(𝒜.toFinset # t) = 1 ∧ ∀ j : Fin (n + 1), s < j ∧ j < t → #(𝒜.toFinset # j) = 0 := by sorry

lemma count_maxChainsThrough (h_mn : m ≤ n + 1) (hn : Fintype.card α = n)
    (cardℬ : #ℬ.toFinset = m) (chainℬ : IsChain (· ⊂ ·) ℬ) (empty_in_chain : ∅ ∈ ℬ) (univ_in_chain : univ ∈ ℬ)
    (list : List (Finset α)) (list_per : ℬ.toFinset.toList ~ list) (list_sorted : list.Sorted (#· < #·)):
    Fintype.card (MaxChainThrough ℬ) = ∏ j : Fin (list.length - 1), (#list[j.val + 1] - #list[j.val])! := by
  revert ℬ list
  induction' h_mn using decreasingInduction with n_ q ih
  · intro ℬ cardℬ chainℬ empty_in_chain univ_in_chain list list_per list_sorted

    let sorted_list := ((univ : Finset ℬ).toList.insertionSort (fun (e₁ e₂ : ℬ) ↦ #e₁.val ≤ #e₂.val))

    obtain ⟨s', t', empty_range : s'.val + 2 ≤ t'.val ∧ #(ℬ.toFinset # s') = 1 ∧ #(ℬ.toFinset # t') = 1 ∧ ∀ (j : Fin (n + 1)), s' < j ∧ j < t' → #(ℬ.toFinset # ↑j) = 0⟩ :=
      range_empty_layer hn chainℬ (by sorry) empty_in_chain univ_in_chain

    let s : range (n + 1) := ⟨s'.val, mem_range.mpr s'.is_lt⟩
    let t : range (n + 1) := ⟨t'.val, mem_range.mpr t'.is_lt⟩

    have ilej_succ_succ : (s : ℕ) + 2 ≤ (t : ℕ) := by simp [empty_range.left]

    obtain ⟨layer_t, ht : (ℬ.toFinset # t) = {layer_t}⟩ := card_eq_one.mp empty_range.right.right.left
    obtain ⟨layer_s, hs : (ℬ.toFinset # s) = {layer_s}⟩ := card_eq_one.mp empty_range.right.left

    have empty_layer' : ∀ j ∈ range (n + 1), s < j → j < t → #(ℬ.toFinset # ↑j) = 0 := by
      simp
      intro j jinrange jgt jlt

      have nsuccnezero : n + 1 ≠ 0 := by simp
      have jmod : j % (n + 1) = j := (mod_eq_iff_lt nsuccnezero).mpr jinrange
      have s'ltj : s' < Fin.ofNat j := by simp [Fin.ofNat, jmod]; exact jgt
      have jltt' : Fin.ofNat j < t' := by simp [Fin.ofNat, jmod]; exact jlt
      have := empty_range.right.right.right j ⟨s'ltj, jltt'⟩
      simp [jmod] at this
      exact this

    have empty_layer : ∀ j : Fin (n + 1), s' < j → j < t' → #(ℬ.toFinset # ↑j) = 0 := by
      simp
      intro j jgt jlt

      have nsuccnezero : n + 1 ≠ 0 := by simp
      have := empty_range.right.right.right j ⟨jgt, jlt⟩
      simp at this
      exact this

    let extension_candidates :=  extension_candidates ℬ layer_s

    have extension_candidates_eq : extension_candidates = layer_t \ layer_s := by
      refine' extension_candidates_characterisation hn ilej_succ_succ chainℬ hs ht empty_layer'

    have layer_s_mem_card := Slice.singleton_explicit.mp hs
    have layer_t_mem_card := Slice.singleton_explicit.mp ht

    have := list_per

    obtain ⟨i_s, ⟨entry_i_s, entry_i_s_succ⟩⟩ := incident_indices_monotone_cards ilej_succ_succ list list_sorted list_per hs ht empty_layer

    have i_s_in_range : i_s < list.length := Nat.lt_of_lt_of_le i_s.is_lt (Nat.pred_le list.length)
    have i_s_succ_in_range : i_s.val + 1 < list.length := add_lt_of_lt_sub i_s.is_lt

    let multiplicant' (j : Fin (list.length - 1)) : ℕ := (#list[j.val + 1] - #list[j.val] - 1)!
    let multiplicant (j : Fin (list.length - 1)) : ℕ := (#list[j.val + 1] - #list[j.val])!

    have extension_candidates_card : #extension_candidates = #list[i_s.val + 1] - #list[i_s.val] := by
      rw [entry_i_s, entry_i_s_succ, layer_s_mem_card.right.left, layer_t_mem_card.right.left]
      rw [extension_candidates_eq]
      have card_bottom_lt_card_top : #layer_s < #layer_t := by
        rw [layer_s_mem_card.right.left, layer_t_mem_card.right.left]
        linarith
      have bottom_subset_top : layer_s ⊂ layer_t :=
        IsChain.ssubset_of_lt_cardinality chainℬ (mem_toFinset.mp layer_s_mem_card.left) (mem_toFinset.mp layer_t_mem_card.left) card_bottom_lt_card_top
      have := card_sdiff_add_card_eq_card bottom_subset_top.left
      rw [←layer_s_mem_card.right.left, ←layer_t_mem_card.right.left]
      exact Nat.eq_sub_of_add_eq this

    let 𝒬 := (univ : Finset (Fin (list.length - 1)))
    let 𝒬' := 𝒬 \ {i_s}

    let extensions_wrt (x : α) : Finset (Set (Finset α)) := by
      let ℬ' : Set (Finset α) := Insert.insert (Insert.insert x layer_s) ℬ
      exact (univ : Finset (MaxChainThrough ℬ')).image (emb_MaxChainThrough ℬ')

    /- Here the induction hypothesis ih is applied-/
    have card_extensions_wrt (a : extension_candidates) : #(extensions_wrt a) = (multiplicant' i_s) * ∏ j ∈ 𝒬', (multiplicant j) := by
      let e_new := Insert.insert (↑a) layer_s
      let ℬ' := (Insert.insert e_new ℬ)

      have a_property₁ := a.prop
      simp only [extension_candidates, Finset.extension_candidates, mem_filter, chain_extension_filter_function] at a_property₁

      have a_property₂ := a.prop
      simp [extension_candidates_eq] at a_property₂

      have card_e_new : #e_new = s + 1 := by
        have := layer_s_mem_card.right.left
        simp [s] at this
        simp [e_new, ←this]
        apply card_insert_of_not_mem
        · exact a_property₂.right

      have ℬ'card : #ℬ'.toFinset = n_ + 1 := by
        simp only [ℬ', ←cardℬ, e_new]
        sorry
        -- have := card_insert_of_not_mem a_property₁.right.right
        -- · exact a_property₁.right.right

      obtain ⟨list', ⟨list_per' : list' ~ (insert e_new ℬ).toFinset.toList, list_sorted' ⟩⟩ := Chain.card_strict_mono a_property₁.right.left
      have embedding_card := card_image_of_injective (univ : Finset (MaxChainThrough ℬ')) inj_emb_MaxChainThrough
      simp [extensions_wrt, embedding_card]

      have empty_in_chain' : ∅ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr empty_in_chain)
      have univ_in_chain' : univ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr univ_in_chain)

      let i_new := list'.indexOf e_new
      have := list_per'.symm.subset (mem_toList.mpr (mem_toFinset.mpr (Set.mem_insert e_new ℬ)))

      have := (mem_toList.mpr (mem_insert_self e_new ℬ.toFinset))
      have i_new_in_range : i_new < list'.length := (List.indexOf_lt_length.mpr (list_per'.symm.subset (mem_toList.mpr (mem_toFinset.mpr (Set.mem_insert e_new ℬ)))))
      have h_i_new : list'[i_new] = e_new := list'.indexOf_get i_new_in_range

      let i_univ := list'.indexOf univ
      have i_univ_in_range : i_univ < list'.length := List.indexOf_lt_length.mpr (list_per'.symm.subset (mem_toList.mpr (mem_toFinset.mpr univ_in_chain')))
      have h_i_univ : list'[i_univ] = univ := list'.indexOf_get i_univ_in_range

      have i_new_lt_i_univ' : (⟨i_new, i_new_in_range⟩ : Fin list'.length) < (⟨i_univ, i_univ_in_range⟩ : Fin list'.length) := by
        by_contra! ass

        have : s'.val + 2 < n + 1 := lt_of_le_of_lt empty_range.left t'.is_lt
        have : s'.val < n + 1 := s'.isLt

        cases lt_or_eq_of_le ass with
        | inl h =>
          have := List.pairwise_iff_get.mp list_sorted' ⟨i_univ, i_univ_in_range⟩ ⟨i_new, i_new_in_range⟩ h
          simp at this
          simp [h_i_new, h_i_univ, card_e_new, hn] at this

          linarith
        | inr h =>
          have : e_new = univ := by
            calc
              e_new = list'[i_new] := h_i_new.symm
              _ = list'[i_univ] := by simp [Fin.mk.inj_iff.mp h]
              _ = univ := h_i_univ
          have : s.val + 1 = n := by
            rw [←card_e_new, ←hn, this]
            rfl
          linarith

      have i_new_lt_i_univ_pred : i_new < list'.length - 1 := Nat.lt_of_lt_of_le i_new_lt_i_univ' (Nat.le_pred_of_lt i_univ_in_range)

      let i_new' : Fin (list'.length - 1) := ⟨i_new, i_new_lt_i_univ_pred⟩
      let i_new'_pred : Fin (list'.length - 1) := ⟨i_new - 1, Nat.lt_of_le_of_lt (Nat.pred_le i_new) i_new_lt_i_univ_pred⟩

      have ind_present : Fintype.card (MaxChainThrough ℬ') = ∏ j : Fin (list'.length - 1), (#list'[j.val + 1] - #list'[j.val])! :=
        ih ℬ'card a_property₁.right.left empty_in_chain' univ_in_chain' list' list_per'.symm list_sorted'

      have product_split : ∏ j : Fin (list'.length - 1), (#list'[j.val + 1] - #list'[j.val])! =
          (#list'[i_new'.val + 1] - #list'[i_new'.val])! * ∏ j ∈ univ \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])! :=
        prod_eq_mul_prod_diff_singleton (by simp) (fun (i : Fin (list'.length - 1)) ↦ (#list'[i.val + 1] - #list'[i.val])!)

      rw [ind_present, product_split]

      have prod_identity : ∏ j ∈ (univ : Finset (Fin (list'.length - 1))) \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])! = ∏ j ∈ 𝒬', multiplicant j := by
        calc
          ∏ j ∈ (univ : Finset (Fin (list'.length - 1))) \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])!
            = (#list'[i_new'_pred.val + 1] - #list'[i_new'_pred.val])! * ∏ j ∈ ((univ : Finset (Fin (list'.length - 1))) \ {i_new'}) \ {i_new'_pred}, (#list'[j.val + 1] - #list'[j.val])! := by
              refine' prod_eq_mul_prod_diff_singleton _ (fun (i : Fin (list'.length - 1)) ↦ (#list'[i.val + 1] - #list'[i.val])!)
              apply mem_sdiff.mpr
              constructor
              · simp
              · unfold i_new'_pred i_new'
                simp
                apply sub_one_ne_self

                have list_first_entry : list'[0] = ∅ := first_entry list' list_sorted' list_per'.symm empty_in_chain'

                by_contra ass

                simp [←ass, h_i_new] at list_first_entry
                unfold e_new at list_first_entry

                have := nonempty_iff_ne_empty.mp (insert_nonempty a.val layer_s)

                exact this list_first_entry

            _ = 1 * ∏ j ∈ ((univ : Finset (Fin (list'.length - 1))) \ {i_new'}) \ {i_new'_pred}, (#list'[j.val + 1] - #list'[j.val])! := by
              congr
              sorry
        sorry
      sorry
      --have mul_identity : multiplicant' i_s = (#list'[↑i_new' + 1] - #list'[↑i_new'])! := by sorry

    have : extension_candidates ≠ ∅ := by
      by_contra! ass
      have equality : #extension_candidates = 0 := by simp [ass]
      rw [extension_candidates_card] at equality

      have : #list[i_s.val + 1] = #list[i_s.val] := by sorry
      have inequality := (pairwise_iff_getElem.mp list_sorted) i_s.val (i_s.val + 1) i_s_in_range i_s_succ_in_range (Nat.lt_succ_self i_s.val)
      linarith

    have central_identity := central_identity layer_s (mem_toFinset.mp layer_s_mem_card.left) (by  sorry)

    have := card_image_of_injective (univ : Finset (MaxChainThrough ℬ)) inj_emb_MaxChainThrough

    rw [Fintype.card, ←this, central_identity, card_disjiUnion]

    calc
      ∑ a ∈ extension_candidates, #(extensions_wrt a) =
          ∑ a ∈ extension_candidates, (multiplicant' i_s) * ∏ j ∈ 𝒬', (multiplicant j) := by
        apply sum_congr (by simp)
        intro x hx
        exact card_extensions_wrt ⟨x, hx⟩
      _ = (multiplicant i_s) *  ∏ j ∈ 𝒬', (multiplicant j) := by
        simp [sum_const, extension_candidates_card, multiplicant']
        rw [←mul_assoc]
        congr
        simp [multiplicant]
        apply mul_factorial_pred _
        · simp [entry_i_s, entry_i_s_succ, layer_s_mem_card.right.left, layer_t_mem_card.right.left]
          have : s'.val < t'.val := by linarith [empty_range.left]
          exact this
      _ = (multiplicant i_s) *  ∏ j ∈ 𝒬', (multiplicant j) := by simp
      _ = ∏ j ∈ 𝒬, (multiplicant j) := by
        simp [𝒬']
        have : i_s ∈ 𝒬 := by simp [𝒬]
        exact (prod_eq_mul_prod_diff_singleton this multiplicant).symm
      _ = ∏ j ∈ 𝒬, (#list[j.val + 1] - #list[j.val])! := by
        apply prod_congr (by simp)
        intro x hx
        rfl

  · intro ℬ cardℬ chainℬ empty_in_chain univ_in_chain list list_perm list_sorted
    have entry_cards : ∀ j : Fin (list.length - 1), #list[j.val] = j.val := by sorry
    have rhs_one := by calc
      ∏ j : Fin (list.length - 1), (#list[j.val + 1] - #list[j.val])! = ∏ j : Fin (list.length - 1), 1 := by
        apply prod_congr (by simp)
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

lemma count_maxChains_through_singleton_insert_empty : Fintype.card (MaxChainThrough ℬ) = Fintype.card (MaxChainThrough (insert ∅ ℬ)) := by sorry

lemma count_maxChains_through_singleton_insert_univ : Fintype.card (MaxChainThrough ℬ) = Fintype.card (MaxChainThrough (insert univ ℬ)) := by sorry

lemma count_maxChains_through_empty (hn : Fintype.card α = n): Fintype.card (MaxChainThrough {(∅ : Finset α)}) = n! := by sorry

lemma count_maxChains_through_univ (hn : Fintype.card α = n): Fintype.card (MaxChainThrough {(Finset.univ : Finset α)}) = n! := by sorry

lemma count_maxChains_through_singleton (e : Finset α) (hn : Fintype.card α = n): Fintype.card (MaxChainThrough {e}) = (#e)! * (n - #e)! := by
  by_cases e_empty : ∅ ≠ e
  · by_cases e_univ : univ ≠ e
    · let 𝒞 : Set (Finset α) := {∅, univ, e}
      have req : #𝒞.toFinset ≤ n + 1 := by sorry
      have empty_in_chain : ∅ ∈ 𝒞 := Set.mem_insert ∅ {univ, e}
      have univ_in_chain : univ ∈ 𝒞 := by sorry
      have chain_singleton : IsChain (· ⊂ ·) 𝒞 := by sorry

      obtain ⟨list, ⟨list_per, list_sorted⟩⟩ := Chain.card_strict_mono chain_singleton

      have := count_maxChainsThrough req hn rfl chain_singleton empty_in_chain univ_in_chain list list_per.symm list_sorted

      rw [count_maxChains_through_singleton_insert_univ, count_maxChains_through_singleton_insert_empty, this]

      have list_length : list.length = 3 := by
        calc
          list.length = 𝒞.toFinset.toList.length := Perm.length_eq list_per
          _ = #𝒞.toFinset := length_toList 𝒞.toFinset
          _ = 𝒞.ncard := Eq.symm (ncard_eq_toFinset_card' 𝒞)
          _ = 3 := by
            refine' ncard_eq_three.mpr _
            use ∅, univ, e
            have : ∅ ≠ (univ : Finset α) := by sorry
            exact ⟨this, e_empty, e_univ, by simp⟩

      sorry
    · sorry
  · sorry





end MaxChainThrough
