import TheBook.ToMathlib.Chain_optional
import TheBook.ToMathlib.Chain
import TheBook.ToMathlib.List

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)} (𝒞₀ : Set α) (𝒞₁ : Finset α) [Fintype 𝒞₀]

namespace Finset

structure MaxChainThrough (ℬ : Finset (Finset α)) where
  𝒜 : Finset (Finset α)
  isMaxChain : Finset.IsMaxChain (· ⊂ ·) 𝒜
  subChain : ℬ ⊆ 𝒜

def emb_MaxChainThrough (ℬ : Finset (Finset α)) (X : ℬ.MaxChainThrough) : Finset (Finset α) := X.𝒜

@[ext] lemma MaxChainThrough_eq {ℬ : Finset (Finset α)} (𝒞₁ 𝒞₂ : ℬ.MaxChainThrough) (hA : 𝒞₁.𝒜 = 𝒞₂.𝒜) : 𝒞₁ = 𝒞₂ := by
  cases 𝒞₁
  cases 𝒞₂
  congr

lemma inj_emb_MaxChainThrough {ℬ : Finset (Finset α)} : Injective (emb_MaxChainThrough ℬ) := by
  intro 𝒞₁ 𝒞₂ h
  unfold emb_MaxChainThrough at h
  ext
  rw [h]

instance instFintypeMaxChainThrough {ℬ : Finset (Finset α)} : Fintype (MaxChainThrough ℬ) := by sorry

variable [Fintype α] [DecidableEq α] [DecidableEq (Finset (Finset α))] [DecidableEq (Finset α)]

def chain_extension_filter_function (𝒜 : Finset (Finset α)) (e : Finset α) : α → Prop :=
  fun a : α ↦ IsChain (· ⊂ ·) (insert (insert a e) 𝒜) ∧ insert a e ∉ 𝒜

instance instDecidableIsChain (𝒜 : Finset (Finset α)) : Decidable (IsChain (· ⊂ ·) 𝒜) := by
  apply Finset.decidableDforallFinset

instance instDecidablePredChainExtension (e : Finset α) :
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

lemma range_empty_layer (hn : Fintype.card α = n) (chain𝒜 : IsChain (· ⊂ ·) 𝒜) (empty_layer : ∃ i : Fin (n + 1), #(𝒜 # i) = 0) (empty_elt : ∅ ∈ 𝒜) (univ_elt : Finset.univ ∈ 𝒜) :
    ∃ s : Fin (n + 1), ∃ t : Fin (n + 1), s.val + 2 ≤ t.val ∧ #(𝒜 # s) = 1 ∧ #(𝒜 # t) = 1 ∧ ∀ j : Fin (n + 1), s < j ∧ j < t → #(𝒜 # j) = 0 := by sorry

lemma mem_card_of_slice {ℬ : Finset (Finset α)} (h : (ℬ # s) = {layer_s}) : layer_s ∈ ℬ ∧ #layer_s = s := by
  have := Finset.mem_singleton_self layer_s
  rw [←h] at this
  simp [slice] at this
  exact this

lemma extension_candidates_characterisation (hn : Fintype.card α = n) {i j : Finset.range (n + 1)} (ilej_succ_succ : (i : ℕ) + 2 ≤ (j : ℕ)) (chain𝒜 : IsChain (· ⊂ ·) 𝒜)
    (hi : (𝒜 # i) = {layer_i}) (hj : (𝒜 # j) = {layer_j}) (emptylayer : ∀ l ∈ (Finset.range (n + 1)), i < l → l < j → #(𝒜 # l) = 0):
    extension_candidates 𝒜 layer_i = layer_j \ layer_i := by
  unfold extension_candidates

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

lemma first_entry {ℬ : Finset (Finset α)} (list : List (Finset α))
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toList ~ list)
    (empty_in_chain : ∅ ∈ ℬ) : list[0]'(by sorry) = ∅ := by sorry

lemma last_entry {list : List (Finset α)} {ℬ : Finset (Finset α)}
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toList ~ list)
    (univ_in_chain : univ ∈ ℬ) : list[list.length - 1]'(by sorry) = univ := by sorry

lemma incident_indices_monotone_cards {n: ℕ} {s t : Fin (n + 1)} {ℬ : Finset (Finset α)} (ilej_succ_succ : s.val + 2 ≤ t.val) (list : List (Finset α))
    (monotone_cards: List.Sorted (fun (e₁ e₂) ↦ #e₁ < #e₂) list) (h_list: ℬ.toList ~ list)
    (hs : (ℬ # s) = {layer_s}) (ht : (ℬ # t) = {layer_t})
    (empty_layer : ∀ j : Fin (n + 1), s < j → j < t → #(ℬ # ↑j) = 0) :
    ∃ i_s : Fin (list.length - 1), list[i_s.val]  = layer_s ∧ list[i_s.val + 1] = layer_t := by

  let i_s := list.indexOf layer_s
  have i_s_in_range : i_s < list.length := List.indexOf_lt_length.mpr (h_list.subset (mem_toList.mpr (mem_card_of_slice hs).left))
  have h_i_s : list[i_s] = layer_s := list.indexOf_get i_s_in_range

  let i_t := list.indexOf layer_t
  have i_t_in_range : i_t < list.length := List.indexOf_lt_length.mpr (h_list.subset (mem_toList.mpr (mem_card_of_slice ht).left))
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
        simp [←(mem_card_of_slice hs).right, ←(mem_card_of_slice ht).right]
        exact this
      linarith
    have i_s_succ_lt : i_s + 1 < i_t := Nat.lt_of_le_of_ne this fun a => ass₁ (id (Eq.symm a))

    let e := list[i_s + 1]

    have e_card_gt' : #e > s := by
      have := (List.pairwise_iff_get.mp monotone_cards) ⟨i_s, by simpa⟩ ⟨i_s + 1, by apply Nat.lt_trans i_s_succ_lt; simpa ⟩ (by simp : i_s < i_s + 1)
      simp [h_i_s, (mem_card_of_slice hs).right] at this
      unfold e
      exact this

    have e_card_lt' : #e < t := by
      have := (List.pairwise_iff_get.mp monotone_cards) ⟨i_s + 1, by apply Nat.lt_trans i_s_succ_lt; simpa⟩ ⟨i_t, by simpa⟩ i_s_succ_lt
      simp [h_i_t, (mem_card_of_slice ht).right] at this
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

def extensions_wrt (ℬ : Finset (Finset α)) (e : Finset α) (x : α) : Finset (Finset (Finset α)) := by
  let ℬ' : Finset (Finset α) := Insert.insert (Insert.insert x e) ℬ
  exact (Finset.univ : Finset ℬ'.MaxChainThrough).image (emb_MaxChainThrough ℬ')

lemma chain_through_extension_candidates_pairwiseDisjoint (ℬ : Finset (Finset α)) (e : Finset α) (e_mem : e ∈ ℬ) : PairwiseDisjoint (extension_candidates ℬ e) (extensions_wrt ℬ e) := by
  intro x hx y hy xneqy
  simp [_root_.Disjoint]
  simp [extensions_wrt]
  intro A hA_x hA_y
  intro 𝒜 h𝒜
  have a_extension_e_x := hA_x h𝒜
  have a_extension_e_y := hA_y h𝒜

  sorry

lemma central_identity {ℬ : Finset (Finset α)} (e : Finset α) (e_mem : e ∈ ℬ) :
  Finset.univ.image (emb_MaxChainThrough ℬ) = (extension_candidates ℬ e).disjiUnion (extensions_wrt ℬ e)
  (chain_through_extension_candidates_pairwiseDisjoint ℬ e e_mem) := by sorry

lemma count_maxChainsThrough {n: ℕ} (m : ℕ) (h_mn : m ≤ n + 1) (hn : Fintype.card α = n)
    (ℬ : Finset (Finset α)) (cardℬ : #ℬ = m) (chainℬ : IsChain (· ⊂ ·) ℬ) (empty_in_chain : ∅ ∈ ℬ) (univ_in_chain : univ ∈ ℬ)
    (list : List (Finset α)) (list_per : ℬ.toList ~ list) (list_sorted : list.Sorted (#· < #·)):
    Fintype.card (ℬ.MaxChainThrough) = ∏ j : Fin (list.length - 1), (#list[j.val + 1] - #list[j.val])! := by
  revert ℬ list
  induction' h_mn using decreasingInduction with n_ q ih
  · intro ℬ cardℬ chainℬ empty_in_chain univ_in_chain list list_sorted list_per

    let sorted_list := ((Finset.univ : Finset ℬ).toList.insertionSort (fun (e₁ e₂ : ℬ) ↦ #e₁.val ≤ #e₂.val))

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
      refine' extension_candidates_characterisation hn ilej_succ_succ chainℬ hs ht empty_layer'

    have layer_s_mem_card := mem_card_of_slice hs
    have layer_t_mem_card := mem_card_of_slice ht

    have := list_per

    obtain ⟨i_s, ⟨entry_i_s, entry_i_s_succ⟩⟩ := incident_indices_monotone_cards ilej_succ_succ list list_per list_sorted hs ht empty_layer

    have i_s_in_range : i_s < list.length := Nat.lt_of_lt_of_le i_s.is_lt (Nat.pred_le list.length)
    have i_s_succ_in_range : i_s.val + 1 < list.length := add_lt_of_lt_sub i_s.is_lt

    let multiplicant' (j : Fin (list.length - 1)) : ℕ := (#list[j.val + 1] - #list[j.val] - 1)!
    let multiplicant (j : Fin (list.length - 1)) : ℕ := (#list[j.val + 1] - #list[j.val])!

    have extension_candidates_card : #extension_candidates = #list[i_s.val + 1] - #list[i_s.val] := by
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

    let 𝒬 := (Finset.univ : Finset (Fin (list.length - 1)))
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

      obtain ⟨list', ⟨list_per' : list' ~ (insert e_new ℬ).toList, list_sorted' ⟩⟩ := IsChain.card_strict_mono a_property₁.right.left
      have embedding_card := Finset.card_image_of_injective (Finset.univ : Finset (MaxChainThrough ℬ')) inj_emb_MaxChainThrough
      simp [extensions_wrt, embedding_card]

      have empty_in_chain' : ∅ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr empty_in_chain)
      have univ_in_chain' : univ ∈ ℬ' := by simp [ℬ']; exact mem_insert_iff.mpr (Or.inr univ_in_chain)

      let i_new := list'.indexOf e_new
      have := list_per'.symm.subset (mem_toList.mpr (mem_insert_self e_new ℬ))

      have := (mem_toList.mpr (mem_insert_self e_new ℬ))
      have i_new_in_range : i_new < list'.length := (List.indexOf_lt_length.mpr (list_per'.symm.subset (mem_toList.mpr (mem_insert_self e_new ℬ))))
      have h_i_new : list'[i_new] = e_new := list'.indexOf_get i_new_in_range

      let i_univ := list'.indexOf univ
      have i_univ_in_range : i_univ < list'.length := List.indexOf_lt_length.mpr (list_per'.symm.subset (mem_toList.mpr univ_in_chain'))
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

      have ind_present : Fintype.card (ℬ'.MaxChainThrough) = ∏ j : Fin (list'.length - 1), (#list'[j.val + 1] - #list'[j.val])! :=
        ih ℬ' ℬ'card a_property₁.right.left empty_in_chain' univ_in_chain' list' list_per'.symm list_sorted'

      have product_split : ∏ j : Fin (list'.length - 1), (#list'[j.val + 1] - #list'[j.val])! =
          (#list'[i_new'.val + 1] - #list'[i_new'.val])! * ∏ j ∈ univ \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])! :=
        Finset.prod_eq_mul_prod_diff_singleton (by simp) (fun (i : Fin (list'.length - 1)) ↦ (#list'[i.val + 1] - #list'[i.val])!)

      rw [ind_present, product_split]

      have prod_identity : ∏ j ∈ (Finset.univ : Finset (Fin (list'.length - 1))) \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])! = ∏ j ∈ 𝒬', multiplicant j := by
        calc
          ∏ j ∈ (Finset.univ : Finset (Fin (list'.length - 1))) \ {i_new'}, (#list'[j.val + 1] - #list'[j.val])!
            = (#list'[i_new'_pred.val + 1] - #list'[i_new'_pred.val])! * ∏ j ∈ ((Finset.univ : Finset (Fin (list'.length - 1))) \ {i_new'}) \ {i_new'_pred}, (#list'[j.val + 1] - #list'[j.val])! := by
              refine' Finset.prod_eq_mul_prod_diff_singleton _ (fun (i : Fin (list'.length - 1)) ↦ (#list'[i.val + 1] - #list'[i.val])!)
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

                have := nonempty_iff_ne_empty.mp (Finset.insert_nonempty a.val layer_s)

                exact this list_first_entry

            _ = 1 * ∏ j ∈ ((Finset.univ : Finset (Fin (list'.length - 1))) \ {i_new'}) \ {i_new'_pred}, (#list'[j.val + 1] - #list'[j.val])! := by
              congr
              sorry
        sorry
      sorry
      -- have mul_identity : multiplicant' i_s = (#list'[↑i_new' + 1] - #list'[↑i_new'])! := by sorry


    have central_identity := central_identity layer_s layer_s_mem_card.left

    have := Finset.card_image_of_injective (Finset.univ : Finset ℬ.MaxChainThrough) inj_emb_MaxChainThrough

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
      _ = ∏ j ∈ 𝒬, (#list[j.val + 1] - #list[j.val])! := by
        apply prod_congr (by simp)
        intro x hx
        rfl

  · intro ℬ cardℬ chainℬ empty_in_chain univ_in_chain list list_sorted list_perm
    have entry_cards : ∀ j : Fin (list.length - 1), #list[j.val] = j.val := by sorry
    have rhs_one := by calc
      ∏ j : Fin (list.length - 1), (#list[j.val + 1] - #list[j.val])! = ∏ j : Fin (list.length - 1), 1 := by
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
