import Mathlib.Tactic
import Mathlib.Data.List.Perm.Basic

variable {α : Type*} (r : α → α → Prop) [LE α] [DecidableRel (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)]

theorem List.Nodup.orderedInsert
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

theorem List.Nodup.insertionSort {l : List α} (h : l.Nodup) : (l.insertionSort (fun (x₁ x₂ : α) ↦ x₁ ≤ x₂)).Nodup := by
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
