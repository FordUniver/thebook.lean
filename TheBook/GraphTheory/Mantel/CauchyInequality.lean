import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
-- import Mathlib.Tactic.Basic
import Aesop

set_option trace.aesop true
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
local notation "χ(" p ")" => if p then 1 else 0
local notation "n" => Fintype.card V'

-- attribute [simp] Nat.pow_two
-- attribute [simp] Finset.sum_congr
attribute [aesop safe] Finset.mul_sum
attribute [aesop safe] Finset.card_eq_sum_ones
attribute [aesop safe] SimpleGraph.adj_symm
attribute [aesop safe] SimpleGraph.Adj.ne'
attribute [aesop safe] sq_sum_le_card_mul_sum_sq
attribute [aesop safe] HMul.hMul
attribute [aesop safe] MonovaryOn.sum_mul_sum_le_card_mul_sum
attribute [aesop safe] AntivaryOn.card_mul_sum_le_sum_mul_sum
  
example (e : E') (v : V'): ∑ w ∈ V, χ(s(v,w) = e) = χ(v ∈ e) := by
  sorry

example (e : E') : ∑ v ∈ V, χ(v ∈ e) ≤ 2 := by
  sorry

example (e : E') (he : e ∈ E): ∑ v ∈ V, χ(v ∈ e) = 2 := by
  sorry

lemma deg_sum_edges (v : V') : d(v) = ∑ e ∈ E, χ(v ∈ e) := by
  calc d(v)
    _ = #{w | G.Adj v w}.toFinset        := rfl
    _ = ∑ w ∈ V, ∑ e ∈ E, χ(s(v,w) = e)  := by simp
    _ = ∑ e ∈ E, ∑ w ∈ V, χ(s(v,w) = e)  := Eq.symm Finset.sum_comm
    _ = ∑ e ∈ E, χ(v ∈ e)                := by sorry -- FIX

lemma handshake : ∑ v ∈ V, d(v) = 2 * #E := by
  calc  ∑ v ∈ V, d(v)
  _ = ∑ v ∈ V, ∑ e ∈ E, χ(v ∈ e)    := by simp [deg_sum_edges]
  _ = ∑ e ∈ E, ∑ v ∈ V, χ(v ∈ e)    := Eq.symm Finset.sum_comm
  _ = ∑ e ∈ E, 2                    := by sorry -- FIX
  _ = 2 * ∑ e ∈ E, 1                := Eq.symm (Finset.mul_sum E (λ i ↦ 1) 2)
  _ = 2 * #E                        := by simp

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

    obtain ⟨k, h⟩ := Finset.card_pos.mp (Nat.lt_add_left_iff_pos.mp (Nat.lt_of_lt_of_le hc this))
    simp at h
    obtain ⟨hik, hjk⟩ := h

    -- -- But then i, j, k would form a triangle, contradicting the assumption that G has no 3-cliques
    have has_card : #{k, j, i} = 3 := by
      apply SimpleGraph.Adj.ne' at hij
      apply SimpleGraph.Adj.ne' at hik
      apply SimpleGraph.Adj.ne' at hjk
      aesop
      -- simp [hij, hik, hjk]

    exact h {k, j, i} ⟨by aesop, has_card⟩ 

  let sum_deg (e : E') : ℕ := Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  have t1 : n^2 * ∑ (e ∈ E), 1 = n * ∑ (e ∈ E), n := by
    have : n * ∑ (e ∈ E), 1 = ∑ (e ∈ E), n * 1 := Finset.mul_sum E (λ i ↦ 1) n
    have : n * (n * ∑ (e ∈ E), 1) = n * (∑ (e ∈ E), n) := by aesop
    linarith

  have t2 (e : E') (he: e ∈ E) : sum_deg e ≤ n := by obtain ⟨i, j⟩ := e; aesop

  have deg_eq_ind_sum (e : E') (he: e ∈ E) : sum_deg e = ∑ (v ∈ V), d(v) * (if v ∈ e then 1 else 0) := by sorry
  
  have t3 : ∑ (e ∈ E), sum_deg e = ∑ (v ∈ V), d(v)^2 := by
    calc  ∑ (e ∈ E), sum_deg e
    _ =  ∑ (e ∈ E), ∑ (v ∈ V), d(v) * (if v ∈ e then 1 else 0) := Finset.sum_congr rfl deg_eq_ind_sum
    _ =  ∑ (v ∈ V), (∑ (e ∈ E), (d(v) * (if v ∈ e then 1 else 0))) := Finset.sum_comm
    _ =  ∑ (v ∈ V), (d(v) * (∑ (e ∈ E), (if v ∈ e then 1 else 0))) := Finset.sum_congr rfl (λ v a ↦ Eq.symm (Finset.mul_sum E (λ i ↦ if v ∈ i then 1 else 0) d(v)))
    _ =  ∑ (v ∈ V), d(v)^2 := Finset.sum_congr rfl sorry

  have t4 : (∑ (v ∈ V), d(v))^2 ≤ n * ∑ (v ∈ V), d(v)^2 := by
    sorry --FIX
    -- have := @sq_sum_le_card_mul_sum_sq V' ℝ _ V (λ v ↦ G.degree v)
    -- this is effectively what we want, but with annoying casting ...
    -- sorry

  -- We slightly modify the argument to avoid division (in particular by zero)
  have t5 := calc n^2 * #E
    _ = n^2 * ∑ (e ∈ E), 1          := by simp
    _ = n * ∑ (e ∈ E), n            := t1 --FIX
    _ ≥ n * ∑ (e ∈ E), sum_deg e    := Nat.mul_le_mul_left n (Finset.sum_le_sum t2) -- FIX
    _ = n * ∑ (v ∈ V), d(v)^2       := by simp [t3] -- FIX
    _ ≥ (∑ (v ∈ V),  d(v))^2        := t4 -- FIX
    _ = (2 * #E)^2                  := by simp [handshake]
    _ = 4 * #E^2                    := by linarith

  -- now show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · exact le_of_eq_of_le hE (Nat.zero_le (n ^ 2 / 4))
  · push_neg at hE
    have t₇ : n ^ 2 * #E ≥ (4 * #E) * #E := by linarith
    have : n ^ 2 ≥ 4 * #E := Nat.le_of_mul_le_mul_right t₇ (Nat.zero_lt_of_ne_zero hE) 
    have : 4 > 0 := Nat.zero_lt_succ 3
    sorry --FIX

-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry


end CauchyMantelTheorem
