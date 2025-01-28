import TheBook.Combinatorics.SpernerHelpingDataStructures

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} {𝒜 : Finset (Finset α)} [DecidableEq α]

namespace Finset

lemma AntiChain.disj_union_chain_through (anti_chain : IsAntichain (· ⊂ ·) 𝒜) :
    𝒜.toSet.PairwiseDisjoint (fun e ↦ ((Finset.univ : Finset (MaxChainThrough {e})).image (emb_MaxChainThrough {e}))) := by
  intro e₁ e₁_mem_𝒜 e₂ e₂_mem_𝒜 e₁neqe₂
  simp [onFun]

  refine' disjoint_left.mpr _
  intro C C_mem₁ C_mem₂

  obtain ⟨C₁, ⟨_, C₁_image⟩⟩ := mem_image.mp C_mem₁
  obtain ⟨C₂, ⟨_, C₂_image⟩⟩ := mem_image.mp C_mem₂

  have e₁_mem_C₁ := singleton_subset_iff.mp C₁.subChain
  have e₂_mem_C₂ := singleton_subset_iff.mp C₂.subChain
  unfold emb_MaxChainThrough at C₁_image C₂_image
  rw [C₂_image, ←C₁_image] at e₂_mem_C₂

  have comparable := C₁.isMaxChain.left e₁_mem_C₁ e₂_mem_C₂ e₁neqe₂
  simp at comparable

  have noncomparable₁ := anti_chain e₁_mem_𝒜 e₂_mem_𝒜 e₁neqe₂
  have noncomparable₂ := anti_chain e₂_mem_𝒜 e₁_mem_𝒜 e₁neqe₂.symm
  simp at noncomparable₁
  simp at noncomparable₂

  cases comparable with
  | inl h => exact noncomparable₁ h
  | inr h => exact noncomparable₂ h
