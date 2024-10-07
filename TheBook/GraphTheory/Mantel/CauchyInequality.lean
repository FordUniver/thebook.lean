import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Aesop

set_option autoImplicit false


prefix:100 "#" => Finset.card
set_option linter.unusedSectionVars false

namespace CauchyMantelTheorem

variable {V' : Type*} [Fintype V'] [DecidableEq V']
variable {G : SimpleGraph V'} [DecidableRel G.Adj]

local notation "V" => @Finset.univ V' _
abbrev E' := Sym2 V'
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "n" => Fintype.card V'

theorem mantel (h: G.CliqueFree 3) : #E ≤ (n^2 / 4) := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have adj_degree_bnd (i j : V') (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Otherwise there would exist a vertex k adjacent to both i and j by pigeonhole principle
    by_contra hc
    simp at hc

    have : #(N(i) ∩ N(j)) + n ≥ #N(i) + #N(j) := by
      have : #(N(i) ∩ N(j)) + #(N(i) ∪ N(j)) = #N(i) + #N(j) := Finset.card_inter_add_card_union _ _
      have : #(N(i) ∪ N(j)) ≤ n := Finset.card_le_univ _
      linarith

    have : #(N(i) ∩ N(j)) > 0 := (Nat.lt_add_left_iff_pos.mp (Nat.lt_of_lt_of_le hc this))

    have ⟨k, hik, hjk⟩ : ∃ k : V', G.Adj i k ∧ G.Adj j k := by
      obtain ⟨k, h⟩ := Finset.card_pos.mp this
      simp [Set.mem_inter_iff] at h
      exact Exists.intro k h

    -- But then i, j, k would form a triangle, contradicting the assumption that G has no 3-cliques
    have is_clique : G.IsClique {i, j, k} := by
      intros x hx y hy hxney
      all_goals rcases hx with rfl | rfl | rfl <;> 
                rcases hy with rfl | rfl | rfl <;> 
                simp [hij, hik, hjk, G.adj_symm hij, G.adj_symm hik, G.adj_symm hjk] <;> 
                exact False.elim (hxney rfl)

    have has_card : #{i, j, k} = 3 := by
      simp [SimpleGraph.Adj.ne' (id (G.adj_symm hij)), SimpleGraph.Adj.ne' (id (G.adj_symm hik)), SimpleGraph.Adj.ne' (id (G.adj_symm hjk))]

    exact h {i, j, k} ⟨by simp [is_clique], has_card⟩ 

  let sum_deg (e : E') : ℕ := Sym2.lift ⟨λ x y => d(x) + d(y), by simp [Nat.add_comm]⟩ e

  have t1 : n^2 * ∑ (e ∈ E), 1 = n * ∑ (e ∈ E), n := by
    have : n * ∑ (e ∈ E), 1 = ∑ (e ∈ E), n * 1 := Finset.mul_sum E (fun i => 1) n
    have : ∑ (e ∈ E), n * 1 = ∑ (e ∈ E), n := by simp
    have : n * ∑ (e ∈ E), 1 = ∑ (e ∈ E), n := by linarith
    have : n * (n * ∑ (e ∈ E), 1) = n * (∑ (e ∈ E), n) := congrArg (HMul.hMul n) this
    linarith

  have t2 (e : E') (he: e ∈ E) : sum_deg e ≤ n := by
    obtain ⟨i, j⟩ := e
    exact adj_degree_bnd _ _ ((SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp he))

  have t3 : ∑ (e ∈ E), sum_deg e = ∑ (v ∈ V), d(v)^2 := by
    -- seems like double counting again?
    sorry

  have t4 : (∑ (v ∈ V), d(v))^2 ≤ n * ∑ (v ∈ V), d(v)^2 := by
    have := @sq_sum_le_card_mul_sum_sq V' ℝ _ V (λ v => G.degree v)
    -- this is effectively what we want, but with annoying casting ...
    sorry

  -- We slightly modify the argument to avoid division (in particular by zero)
  have t5 := calc n^2 * #E
    _ = n^2 * ∑ (e ∈ E), 1          := by simp
    _ = n * ∑ (e ∈ E), n            := t1 --replace
    _ ≥ n * ∑ (e ∈ E), sum_deg e    := Nat.mul_le_mul_left n (Finset.sum_le_sum t2) --replace
    _ = n * ∑ (v ∈ V), d(v)^2       := by simp [t3] --replace
    _ ≥ (∑ (v ∈ V),  d(v))^2        := t4 -- replace
    _ = (2 * #E)^2                  := by simp [SimpleGraph.sum_degrees_eq_twice_card_edges]
    _ = 4 * #E^2                    := by linarith

  -- now show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · exact le_of_eq_of_le hE (Nat.zero_le (n ^ 2 / 4))
  · have t₇ : n ^ 2 * #E ≥ (4 * #E) * #E := by linarith
    have : n ^ 2 ≥ 4 * #E := Nat.le_of_mul_le_mul_right t₇ (Nat.zero_lt_of_ne_zero hE) 
    have : 4 > 0 := Nat.zero_lt_succ 3
    sorry

-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry


end CauchyMantelTheorem
