import Mathlib.Tactic
import Mathlib.Data.List.Perm.Basic

open Function Finset Nat Set BigOperators List

section Nodup

variable {α : Type*} (r : α → α → Prop) [LE α] [DecidableRel (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)]

lemma List.Nodup.orderedInsert
  {l : List α} {a : α} (l_nodup : l.Nodup) (a_not_mem : a ∉ l) :
  (orderedInsert (· ≤ ·) a l).Nodup := by
  induction l with
  | nil =>
    simp [orderedInsert]
  | cons x xs ih =>
    simp [orderedInsert]
    simp at a_not_mem
    simp at l_nodup
    split
    · simp [List.Nodup]
      constructor
      · constructor
        · exact a_not_mem.left
        · intro u hu
          by_contra ass
          rw [←ass] at hu
          exact a_not_mem.right hu
      · constructor
        · intro u hu
          by_contra ass
          rw [←ass] at hu
          exact l_nodup.left hu
        · exact l_nodup.right
    · simp
      constructor
      · constructor
        · exact fun x ↦ a_not_mem.left x.symm
        · exact l_nodup.left
      · exact ih l_nodup.right a_not_mem.right

lemma List.Nodup.insertionSort {l : List α} (h : l.Nodup) : (l.insertionSort (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)).Nodup := by
  induction l with
  | nil =>
    simp [List.insertionSort, List.Nodup]
  | cons x xs ih =>
    simp [List.insertionSort]
    have sorted_nodup : (xs.insertionSort (fun x₁ x₂ => x₁ ≤ x₂)).Nodup := ih h.tail
    have x_ne_mem_sorted : x ∉ xs.insertionSort (fun x₁ x₂ => x₁ ≤ x₂) := by
      by_contra ass
      simp at h
      exact h.left ((List.mem_insertionSort (· ≤ ·)).mp ass)
    exact List.Nodup.orderedInsert sorted_nodup x_ne_mem_sorted

end Nodup

section Perm

variable {α : Type*} {𝒜 : Finset α} [DecidableEq α]

lemma Finset.subtype_toList : List.map Subtype.val (Finset.univ : Finset 𝒜).toList ~ 𝒜.toList := by
  refine' perm_iff_count.mpr _
  intro a
  by_cases h : a ∈ 𝒜
  case pos =>
    have count_rhs := nodup_iff_count_eq_one.mp 𝒜.nodup_toList a (mem_toList.mpr h)
    have count_lhs₀ := count_map_of_injective (Finset.univ : Finset 𝒜).toList Subtype.val Subtype.val_injective ⟨a, h⟩
    have count_lhs₁ := nodup_iff_count_eq_one.mp (Finset.univ : Finset 𝒜).nodup_toList ⟨a, h⟩ (mem_toList.mpr (by simp))
    rw [count_rhs, count_lhs₀, count_lhs₁]
  case neg =>
    have count_rhs := List.count_eq_zero_of_not_mem (fun ass ↦ h (mem_toList.mp ass))
    have count_lhs : List.count a (List.map Subtype.val (Finset.univ : Finset 𝒜).toList) = 0 := by
      apply List.count_eq_zero_of_not_mem
      by_contra! ass
      obtain ⟨x, ⟨x_mem_list, x_eq_a⟩⟩ := List.mem_map.mp ass

      have := x.prop
      rw [x_eq_a] at this
      exact h this

    rw [count_rhs, count_lhs]
end Perm
