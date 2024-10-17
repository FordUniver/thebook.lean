import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.MeanInequalities -- has am-gm
import TheBook.ToMathlib.WeightedDoubleCounting


variable {α : Type*} (G : SimpleGraph α)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}


-- An independent set in a graph is a set of vertices that are pairwise nonadjacent.
abbrev IsIndependentSet (G : SimpleGraph α) (s : Set α) : Prop :=
  s.Pairwise (fun a b => ¬ G.Adj a b)


-- All independent sets of a graph.
def allIndependentSets : Finset (Finset α) := {s | IsIndependentSet G s}

-- TODO these could go in a common file, no?
local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card α

prefix:100 "#" => Finset.card
--set_option trace.Meta.Tactic.simp true


-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
lemma neighbors_independent (h: G.CliqueFree 3) : IsIndependentSet G N(i) := by
  by_contra nind
  rw [IsIndependentSet, Set.Pairwise] at nind
  rw [SimpleGraph.CliqueFree] at h
  aesop -- TODO why yello! is aesop even ok?
  have : (i ≠ w) := by aesop
  have : (i ≠ w_1) := by aesop
  exact h {i, w, w_1} ⟨ by aesop , by aesop ⟩


-- TODO can i say A is a maximal independent set in a less verbose way plz
-- The degree of a vertex i is less or equal α, the size of a largest independent set.
lemma degreeLeqa (h: G.CliqueFree 3) (A : Finset α) :
    (∀ B ∈ (allIndependentSets G), #B ≤ #A) → d(i) ≤ #A := by
  have : N(i) ∈ allIndependentSets G := by rw [allIndependentSets]; -- TODO why ∈ so difficult!
                                            aesop;
                                            apply neighbors_independent;
                                            apply h
  intro maxA
  apply maxA N(i) this


-- The set B = V \ A meets every edge of G.
lemma B_meets_every_edge {A : Finset α} (indA : IsIndependentSet G A) :
    (∀ I ∈ (allIndependentSets G), #I ≤ #A) → (∀ e ∈ E, 1 ≤ #{ b ∈ (V \ A) | b ∈ e }) := by

    intro maxA e edgee

    by_contra c
    simp at c
    have b_nin_e : ∀ b ∈ (V \ A) , ¬ (b ∈ e) := Finset.filter_eq_empty_iff.mp c
    induction e with | _ v w => -- TODO is this really how we deconstruct?!
     by_cases vinA : v ∈ (V \ A) -- TODO uglyyy
     . have : w ∈ (V \ A) := by by_contra _; apply (b_nin_e _ vinA); simp
       apply (b_nin_e _ this)
       simp
     . have : w ∉ (V \ A) := by by_contra wninA; apply (b_nin_e _ wninA); simp
       rw [IsIndependentSet] at indA
       aesop


-- We count the edges of G by counting the endvertices in B.
lemma count_edges_by_B {A : Finset α} (indA : IsIndependentSet G A) :
    (∀ I ∈ (allIndependentSets G), #I ≤ #A) → #E ≤ ∑ i ∈ V \ A, d(i) := by

   -- The number of edges adjacent to i is the degree of i. -- TODO duh?
   have n_adj_edges_eq_deg : ∀ i, #{e ∈ E | i ∈ e} = d(i) := by
     intro i
     rw [Eq.symm (SimpleGraph.card_incidenceFinset_eq_degree G i)]
     rw [SimpleGraph.incidenceFinset_eq_filter]

   intro maxA

   calc
     #E = ∑ e ∈ E, 1                                := by simp
      _ ≤ ∑ e ∈ E, #{ i ∈ (V \ A) | i ∈ e }         := Finset.sum_le_sum
                                                         (B_meets_every_edge _ indA maxA)
      _ = ∑ e ∈ E, ∑ i ∈ {i ∈ (V \ A) | i ∈ e}, 1   := by simp
      _ = ∑ i ∈ V \ A, ∑ e ∈ {e ∈ E | i ∈ e}, 1     := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow _ _ _ _
      _ = ∑ i ∈ V \ A, #{e ∈ E | i ∈ e}             := by simp
      _ = ∑ i ∈ V \ A, d(i)                         := Finset.sum_congr
                                                         (by rfl) (fun i _ => n_adj_edges_eq_deg i)


-- The inequality of the arithmetic and geometric mean.
lemma am_gm (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  have := two_mul_le_add_sq a b -- mathlib version of the am-gm.
  linarith -- is this ok to use?
/- we could also...
  calc 4 * a * b
   _ = (2 * 2) * a * b := by simp only [Nat.reduceMul]
   _ = 2 * (2 * a * b) := by repeat rw [mul_assoc]
   _ = 2 * a * b + 2 * a * b := two_mul _
   _ ≤ (a^2 + b^2) + 2 * a * b := by simp [this]
   _ = (a + b)^2 := by simp [add_sq']
-/


-- Mantel's Theorem
theorem mantel (h: G.CliqueFree 3) (A : Finset α) (indA : IsIndependentSet G A) :
    (∀ B ∈ (allIndependentSets G), #B ≤ #A) → #E ≤ (n^2 / 4) := by

  intro maxA

  have := calc #E
   _ ≤ ∑ i ∈ V \ A, d(i)   := count_edges_by_B G indA maxA
   _ ≤ ∑ _ ∈ V \ A, #A     := Finset.sum_le_sum (fun a _ => degreeLeqa G h A maxA)
   _ = #(V \ A) * #A       := Finset.sum_const _ -- TODO simp can do this, do we prefer simp?
   _ = (#V - #A) * #A      := by simp [Finset.card_sdiff _]

  have := calc #E * 4 -- TODO how annoying
   _ = 4 * #E                 := mul_comm _ _
   _ ≤ 4 * ((#V - #A) * #A)   := by aesop
   _ = 4 * (#V - #A) * #A     := Eq.symm (mul_assoc _ _ _)
   _ ≤ ((#V - #A) + #A)^2     := am_gm (#V - #A) (#A)
   _ = (#V)^2                 := by rw [Nat.sub_add_cancel];
                                    exact (Finset.card_le_card (Finset.subset_univ A))
   _ = n^2                    := by simp

  exact ((Nat.le_div_iff_mul_le' (by simp)).mpr this)
