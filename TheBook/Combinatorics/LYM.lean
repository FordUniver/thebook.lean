import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Slice
import Mathlib.Order.Antichain
import Mathlib.Order.Chain
import Mathlib.Data.List.Perm.Basic
import TheBook.ToMathlib.Chain
import TheBook.ToMathlib.Antichain
import TheBook.ToMathlib.List
import TheBook.Combinatorics.SpernerHelpingDataStructures

open Function Finset Nat Set BigOperators List

variable {α : Type*} {n m : ℕ} [DecidableEq α] [Fintype α] {𝒜 : Set (Finset α)} [DecidablePred (· ∈ 𝒜)] [DecidableEq (Set (Finset α))]
instance : Fintype 𝒜 := setFintype 𝒜

namespace Finset

/-- The **Lubell-Yamamoto-Meshalkin inequality**. Sperner's Theorem follows as in Mathlib.Combinatorics.SetFamily.LYM as a corollary -/
theorem lym_inequality (antichain𝒜 : IsAntichain (· ⊂ ·) 𝒜) (hn : Fintype.card α = n):
    ∑ k ∈ Iic n, #(𝒜.toFinset # k) / (n.choose k : ℚ) ≤ (1 : ℚ) := by
  have : ∑ k ∈ Iic n, #(𝒜.toFinset # k) / (n.choose k : ℚ) ≤ (∑ k ∈ Iic n, #(𝒜.toFinset # k) * (k)! * (n - k)!) * (1 / (n)! : ℚ) := by
    calc
      ∑ k ∈ Iic n, #(𝒜.toFinset # k) / (n.choose k : ℚ) = ∑ k ∈ Iic n, #(𝒜.toFinset # k) * (k)! * (n - k)! * (1 / (n)! : ℚ) := by
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
      _ = (∑ k ∈ Iic n, #(𝒜.toFinset # k) * (k)! * (n - k)!) * (1 / (n)! : ℚ) := by simp [←Finset.sum_mul]
    rfl

  refine' le_trans this _
  rw [mul_one_div]
  apply (div_le_one (by simp [Nat.factorial_pos n])).mpr

  norm_cast

  have slice_partition : Finset.disjiUnion (Iic n) 𝒜.toFinset.slice (Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)) = 𝒜.toFinset := by
    rw [Finset.disjiUnion_eq_biUnion (Iic n) 𝒜.toFinset.slice (Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _))]
    rw [←hn]
    have := biUnion_slice 𝒜.toFinset
    exact this

  calc
    ∑ k ∈ Iic n, #(𝒜.toFinset # k) * (k)! * (n - k)! = ∑ k ∈ Iic n, ∑ e ∈ (𝒜.toFinset # k), (#e)! * (n - #e)! := by
      apply Finset.sum_congr (by simp)
      intro k _
      have hq : ∀ e ∈ (𝒜.toFinset # k), (#e)! * (n - #e)! = (k)! * (n - k)! := by
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
    _ = ∑ e ∈ 𝒜, #((Finset.univ : Finset (MaxChainThrough {e})).image (emb_MaxChainThrough {e})) := by
      apply Finset.sum_congr (by simp)
      intro e e_mem
      rw [Finset.card_image_of_injective (Finset.univ : Finset (MaxChainThrough {e})) inj_emb_MaxChainThrough, Finset.card_univ]
    _ = #(𝒜.toFinset.disjiUnion (fun e : Finset α ↦ (Finset.univ : Finset (MaxChainThrough {e})).image (emb_MaxChainThrough {e})) (by simp [AntiChain.disj_union_chain_through antichain𝒜])) := by sorry
    _ ≤ (n)! := by sorry
