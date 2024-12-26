import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.MeanInequalities -- has am-gm
import TheBook.ToMathlib.IndependentSet
import TheBook.ToMathlib.CliqueNumber
import TheBook.ToMathlib.Nat_le

namespace AMGMMantelTheorem

variable {γ : Type*} (G : SimpleGraph γ)
variable [Fintype γ] [DecidableEq γ] [DecidableRel G.Adj]

local notation "V" => @Finset.univ γ _
local notation "n" => Fintype.card γ
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "I(" v ")" => G.incidenceFinset v
local notation "d(" v ")" => G.degree v

open Finset SimpleGraph

-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) : #E ≤ n^2 / 4 := by

  --  Let `α` be the size of a largest independent set `A`, ...
  let α := SimpleGraph.cocliqueNum G
  let ⟨A, maxA⟩  := G.maximumIndependentSet_exists
  have hA : #A = α := maximumIndependentSet_card_eq_cocliqueNum _ _ maxA

  -- ... and set `β = n - α`.
  let β := n - α
  have hαβ: α + β = n := Nat.add_sub_of_le (le_of_eq_of_le (hA.symm) (card_le_card (subset_univ _)))

  -- The neighbor set of a vertex `i` is an independent set.
  have nbhd_ind_of_triangle_free : ∀ (i : γ), G.IsIndependentSet N(i) := by
    simp [Set.coe_toFinset, G.isIndependentSet_neighborSet_if_triangleFree h, neighborFinset]

  -- The degree of a vertex `i` is less or equal the cardinality of a maximum independent set.
  have degree_le_alpha : ∀ (i : γ) , d(i) ≤ α := fun i => 
    hA ▸ (le_of_le_of_eq (nbhd_ind_of_triangle_free i).card_le_cocliqueNum
                  (G.maximumIndependentSet_card_eq_cocliqueNum A maxA).symm)

  -- The set `B = V \ A` of size `β` meets every edge of `G`.
  let B := V \ A
  have hB : #B = β := by have := card_sdiff (subset_univ A); simp_all [hαβ]

  have one_ge_num_incident_verts : ∀ e ∈ E, 1 ≤ #{ i ∈ B | i ∈ e } := by
    simp only [one_le_card, mem_edgeFinset]
    exact G.compl_independentSet_meets_every_edge maxA.independentSet

  -- We count the edges of `G` by counting the endvertices in `B`.
  have count_edges_by_B := by calc
    #E = ∑ e ∈ E, 1                          := by simp
     _ ≤ ∑ e ∈ E, #{ i ∈ B | i ∈ e }         := sum_le_sum one_ge_num_incident_verts
     _ = ∑ e ∈ E, ∑ i ∈ {i ∈ B | i ∈ e}, 1   := by simp
     _ = ∑ i ∈ B, ∑ e ∈ {e ∈ E | i ∈ e}, 1   := sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _
     _ = ∑ i ∈ B, #{e ∈ E | i ∈ e}           := by simp
     _ = ∑ i ∈ B, d(i)                       := sum_congr rfl fun i _ => by
                                                  rw [(G.card_incidenceFinset_eq_degree i).symm,
                                                        G.incidenceFinset_eq_filter]

  -- The final chain of inequalities.
  have card_E_bound := calc
    #E ≤ ∑ i ∈ B, d(i)      := by exact count_edges_by_B
     _ ≤ ∑ _ ∈ B, α         := sum_le_sum fun _ _ => degree_le_alpha _
     _ = α * β              := by simp [Nat.mul_comm, hB]

  have four_times_card_E_bd := calc 
    4 * #E ≤ 4 * α * β        := by linarith
         _ ≤ (α + β)^2        := four_mul_le_pow_two_add _ _
         _ = n^2              := by simp only [hαβ, Nat.sub_add_cancel]

  exact (Nat.le_div_iff_mul_le_comm Nat.ofNat_pos).mpr four_times_card_E_bd

end AMGMMantelTheorem
