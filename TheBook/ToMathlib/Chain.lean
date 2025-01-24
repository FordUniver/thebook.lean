import TheBook.ToMathlib.Chain_optional
import TheBook.ToMathlib.List

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

lemma IsChain.card_strict_mono (chain𝒜 : IsChain (· ⊂ ·) 𝒜) : ∃ l : List (Finset α), l ~ 𝒜.toList ∧ l.Sorted (#· < #·) := by
  let l' := ((Finset.univ : Finset 𝒜).toList.insertionSort (fun (e₁ e₂ : 𝒜) ↦ #e₁.val ≤ #e₂.val))
  have l'_sorted : l'.Sorted (fun (e₁ e₂ : 𝒜) ↦ #e₁.val < #e₂.val) := card_strict_mono' chain𝒜

  let l := l'.map Subtype.val
  use l
  constructor
  · calc
      l ~ (Finset.univ : Finset 𝒜).toList.map Subtype.val := Perm.map Subtype.val (perm_insertionSort (fun e₁ e₂ => #e₁.val ≤ #e₂.val) (Finset.univ : Finset 𝒜).toList)
      _ ~ 𝒜.toList := by
        sorry
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
