import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
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

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local notation "V" => @Finset.univ α _
local notation "E" => G.edgeFinset
local notation "N(" v ")" => G.neighborFinset v
local notation "d(" v ")" => G.degree v
local notation "χ(" p ")" => if p then 1 else 0
local notation "n" => Fintype.card α


attribute [simp] Nat.pow_two
attribute [simp] Finset.sum_congr
attribute [aesop safe] Finset.mul_sum
attribute [aesop safe] Finset.card_eq_sum_ones
attribute [aesop safe] SimpleGraph.adj_symm
attribute [aesop safe] SimpleGraph.Adj.ne
attribute [aesop safe] sq_sum_le_card_mul_sum_sq
attribute [aesop safe] HMul.hMul
attribute [aesop safe] MonovaryOn.sum_mul_sum_le_card_mul_sum
attribute [aesop safe] AntivaryOn.card_mul_sum_le_sum_mul_sum

-- edges have two vertices
lemma card_edge_eq_two (e : Sym2 α) (he : e ∈ E): #{v | v ∈ e} = 2 := by
  rw [Finset.card_eq_two]
  induction e with | _ v w =>
    use v, w, (by aesop)
    ext; simp

lemma aux (e : Sym2 α) (v : α) : #{w' ∈ V | s(v,w') = e} = χ(v ∈ e) := by
  by_cases hve : v ∈ e
  · simp [hve]
    by_contra hc
    let S := {w' ∈ V | s(v,w') = e}
    have : Sym2.Mem.other hve ∈ S := by aesop
    have := Finset.one_lt_card.mp ((Nat.two_le_iff (#S)).mpr ⟨Finset.card_ne_zero_of_mem this, hc⟩)
    aesop
  · aesop

lemma deg_sum_edges (v : α) : d(v) = ∑ e ∈ E, χ(v ∈ e) := by
  calc d(v)
    _ = #{w | G.Adj v w}.toFinset              := rfl
    _ = ∑ w ∈ V, χ(G.Adj v w)                  := by simp
    _ = ∑ w ∈ V, ∑ e ∈ E, χ(s(v,w) = e)        := by simp
    _ = ∑ e ∈ E, ∑ w ∈ V, χ(s(v,w) = e)        := Finset.sum_comm
    _ = ∑ e ∈ E, ∑ w ∈ {w' ∈ V | s(v,w') = e}, 1   := by simp
    _ = ∑ e ∈ E, #{w' ∈ V | s(v,w') = e}           := by simp
    _ = ∑ e ∈ E, χ(v ∈ e)                      := by simp [aux]

lemma handshake : ∑ v ∈ V, d(v) = 2 * #E := by
  calc  ∑ v ∈ V, d(v)
    _ = ∑ v ∈ V, ∑ e ∈ E, χ(v ∈ e)    := by simp [deg_sum_edges]
    _ = ∑ e ∈ E, ∑ v ∈ V, χ(v ∈ e)    := Eq.symm Finset.sum_comm
    _ = ∑ e ∈ E, #{v | v ∈ e}         := Finset.sum_congr rfl (λ e _ ↦ (Finset.card_filter (λ v ↦ v ∈ e) _).symm)
    _ = ∑ e ∈ E, 2                    := Finset.sum_congr rfl (λ e he ↦ card_edge_eq_two e he)
    _ = 2 * ∑ e ∈ E, 1                := Eq.symm (Finset.mul_sum E (λ _ ↦ 1) 2)
    _ = 2 * #E                        := by simp

lemma cauchyschwarz (f : α → ℕ): n * ∑ v ∈ V, (f v)^2 ≥ (∑ v ∈ V, f v)^2 := by sorry

theorem mantel (h: G.CliqueFree 3) : #E ≤ (n^2 / 4) := by

  -- The degrees of two adjacent vertices cannot sum to more than n
  have adj_degree_bnd (i j : α) (hij: G.Adj i j) : d(i) + d(j) ≤ n := by
    -- Otherwise there would exist a vertex k adjacent to both i and j by pigeonhole principle
    by_contra hc
    simp at hc

    have : #(N(i) ∩ N(j)) + n ≥ #N(i) + #N(j) := by
      have := Finset.card_inter_add_card_union N(i) N(j)
      have := Finset.card_le_univ (N(i) ∪ N(j))
      linarith

    obtain ⟨k, h⟩ := Finset.card_pos.mp (Nat.lt_add_left_iff_pos.mp (Nat.lt_of_lt_of_le hc this))
    simp at h
    obtain ⟨hik, hjk⟩ := h

    -- -- But then i, j, k would form a triangle, contradicting the assumption that G has no 3-cliques
    have has_card : #{k, j, i} = 3 := by
      apply SimpleGraph.Adj.ne' at hij
      apply SimpleGraph.Adj.ne' at hik
      apply SimpleGraph.Adj.ne' at hjk
      simp [hij, hik, hjk]

    exact h {k, j, i} ⟨by aesop, has_card⟩ 

  let sum_deg (e : Sym2 α) : ℕ := Sym2.lift ⟨λ x y ↦ d(x) + d(y), by simp [Nat.add_comm]⟩ e

  have sum_deg_ub (e : Sym2 α) (he: e ∈ E) : sum_deg e ≤ n := by obtain ⟨i, j⟩ := e; aesop

  have aux (e : Sym2 α) (he: e ∈ E) : sum_deg e = ∑ (v ∈ V), d(v) * χ(v ∈ e) := by sorry
  
  have sum_sum_deg_eq_sum_sum_sq : ∑ (e ∈ E), sum_deg e = ∑ (v ∈ V), d(v)^2 := by
    calc  ∑ (e ∈ E), sum_deg e
      _ =  ∑ (e ∈ E), ∑ (v ∈ V), d(v) * χ(v ∈ e)     := Finset.sum_congr rfl aux
      _ =  ∑ (v ∈ V), (∑ (e ∈ E), (d(v) * χ(v ∈ e))) := Finset.sum_comm
      _ =  ∑ (v ∈ V), (d(v) * (∑ (e ∈ E), χ(v ∈ e))) := Finset.sum_congr rfl (λ v a ↦ Eq.symm (Finset.mul_sum E (λ i ↦ χ(v ∈ i)) d(v)))
      _ =  ∑ (v ∈ V), d(v)^2                         := Finset.sum_congr rfl sorry

  -- have t1 : n^2 * ∑ (e ∈ E), 1 = n * ∑ (e ∈ E), n := by
  --   have : n * ∑ (e ∈ E), 1 = ∑ (e ∈ E), n * 1 := Finset.mul_sum E (λ i ↦ 1) n
  --   have : n * (n * ∑ (e ∈ E), 1) = n * (∑ (e ∈ E), n) := by aesop
  --   linarith

  -- We slightly modify the argument to avoid division (in particular by zero)
  have := calc n^2 * #E
    _ = n^2 * ∑ (e ∈ E), 1          := by simp
    _ = (n * n) * ∑ (e ∈ E), 1      := by simp
    _ = n * (n * ∑ (e ∈ E), 1)      := by linarith
    _ = n * (∑ (e ∈ E), n * 1)      := by sorry  -- FIX
    _ = n * (∑ (e ∈ E), n)          := by simp
    _ ≥ n * ∑ (e ∈ E), sum_deg e    := Nat.mul_le_mul_left n (Finset.sum_le_sum sum_deg_ub) -- FIX
    _ = n * ∑ (v ∈ V), d(v)^2       := by simp [sum_sum_deg_eq_sum_sum_sq]
    _ ≥ (∑ (v ∈ V),  d(v))^2        := cauchyschwarz (λ v ↦ d(v))
    _ = (2 * #E)^2                  := by simp [handshake]
    _ = 4 * #E^2                    := by linarith

  -- now show #E ≤ n^2 / 4 by "simply" dividing by 4 * #E
  by_cases hE : #E = 0
  · aesop
  · push_neg at hE
    have t₇ : n ^ 2 * #E ≥ (4 * #E) * #E := by linarith
    have : n ^ 2 ≥ 4 * #E := Nat.le_of_mul_le_mul_right t₇ (Nat.zero_lt_of_ne_zero hE) 
    have : 4 > 0 := Nat.zero_lt_succ 3
    sorry --FIX

-- Probably needs to use floor and ceil to be precise ...
theorem mantel_equality (h: G.CliqueFree 3) : 0 = 0 := by
  sorry


end CauchyMantelTheorem
