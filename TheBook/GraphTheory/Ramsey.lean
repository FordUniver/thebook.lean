import Mathlib.Combinatorics.SimpleGraph.Clique
import TheBook.ToMathlib.InducedClique
import TheBook.ToMathlib.ChooseBound
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

open SimpleGraph Finset Fintype Nat

-- TODOS
-- 5. Change red and blue to notation?
-- 8. Do we really need two base cases? Or is it just a matter of figuring out where to start?
-- 10. Revisit subgraph embedding for the recursive bound
-- 12. Possible notation: R(m,n) = R m n and G[S] = G.induce S

----------------------------------------------------------------------------------------------------
-- Edge colorings
-- Because we are lucky, we only talk about two-colorings of the complete graph here.
-- Those can be represented as graphs on the vertex set, where we consider the edge `(v, w)`
-- to be colored red if they are nonadjacent in the representing graph, and to be colored
-- blue if they are adjacent.

-- variable (C : SimpleGraph V)

-- local notation "red(" s ", " t ")" => ¬ C.Adj s t
-- local notation "blue(" s ", " t ")" => C.Adj s t

-- def red (s : Finset V) (C : SimpleGraph V) := (s.toSet).Pairwise (fun v w => red(v, w))
-- def blue (s : Finset V) (C : SimpleGraph V) := (s.toSet).Pairwise C.Adj

-- @[simp] lemma red_compl (s : Finset V) (C : SimpleGraph V) : red s Cᶜ ↔ blue s C := by
--   simp_rw [red, blue, compl_adj, Set.Pairwise]
--   simp_all only [ne_eq, not_false_eq_true, true_and, not_not]

-- @[simp] lemma blue_compl (s : Finset V) (C : SimpleGraph V) : blue s Cᶜ ↔ red s C := by
--   simp[red, blue, isIndepSet_iff_isClique_of_complement]

----------------------------------------------------------------------------------------------------
-- Definitions of Ramsey property and Ramsey Number

-- TODO the type signatures are verbose. can i somehow define a type that's in all the classes i want
-- but still have inference work?
-- this should do it:
-- class MeFinClass (type : Type*) (N : outParam Nat) extends Fintype type where
--   [toDecidableEq : DecidableEq type]
--   [fin : Fintype type]
--   card : Fintype.card type = N

-- In the book, `ramseyProp N m n` is written as `K_N has property (m, n)`. We write it like this
-- because our edge colors in `K_N` are defined as presence/absence of an edge in a graph on
-- `N` vertices. The book property reads as:
--
--    "...no matter how we color the edges of `K_N` red and blue, there is always a
--    complete subgraph on `m` vertices with all edges colored red or a complete
--    subgraph on `n` vertices with all edges colored blue."
--
-- Which using our definition of colorings translates to:
--
--    "...no matter which graph on `N` vertices we chose, there is always a
--    set of `m` vertices that are all non-adjacent (i.e. red edges) or a set of
--    `n` vertices that are all adjacent (i.e. blue edges)."
def ramseyProp (N m n : ℕ) := ∀ (V : Type) [Fintype V] [DecidableEq V] (_ : Fintype.card V = N),
    ∀ (C : SimpleGraph V) [DecidableRel C.Adj],
    ∃ (s : Finset V), (C.IsNIndepSet m s) ∨ (C.IsNClique n s)

-- Straight from the book:
--    "...we ask for the smallest number `N` (if it exists) with this property
--    — and this is the Ramsey number `R(m, n)`."
-- Note that `sInf ∅ = 0`, so our lean definition does not include "existence" like the paper version.
-- We need to keep that in mind when using our `R`.
noncomputable def R (m n : ℕ) : ℕ := sInf { N | ramseyProp N m n}

----------------------------------------------------------------------------------------------------
-- edge colorings induced by vertex subsets

-- The subgraph that is the entire graph
abbrev SimpleGraph.selfSubgraph {V : Type*} (G : SimpleGraph V) := SimpleGraph.toSubgraph G (fun ⦃_ _⦄ a => a)

-- The subraph induced by a vertex subset
abbrev inducedColoring {V : Type*} (G : SimpleGraph V) (A : Finset V) := G.selfSubgraph.induce A.toSet

----------------------------------------------------------------------------------------------------
-- lemmata

-- The book reads:
--    "It is clear that if `K_N` has property `(m, n)`,
--     then so does every `K_s` with `s ≥ N`."
lemma clear {m n : ℕ} (N s : ℕ) (h : N ≤ s) : ramseyProp N m n → ramseyProp s m n := by
  intros ramseyProp_N W _ _ Wcard C _
  rw [ramseyProp] at *
  rw [← Wcard, ← Fintype.card_fin N] at h

  -- We consider the subgraph induced by embedding `K_N` into `K_s`, choosing some embedding.
  let A : Finset W := map (Trunc.out (Function.Embedding.truncOfCardLE h)) univ
  let C' := C.selfSubgraph.induce A.toSet

  -- Since `K_N` has the Ramsey property, we can find a monochromatic vertex subset in the incuded subgraph.
  have : A.card = N := by simp only [card_map, card_univ, Fintype.card_fin, A]
  have := ramseyProp_N A (by simp [this, Fintype.card_coe])
  obtain ⟨s, red_or_blue⟩ := @this C'.coe (Classical.decRel C'.coe.Adj)

  -- It remains to show that that subset is also monochromatic in the supergraph.
  rcases red_or_blue with ⟨scolor, scard⟩ | ⟨scolor, scard⟩ <;>
    use (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s)
  all_goals simp [scard, isNClique_iff, isNIndepSet_iff, Set.Pairwise] at scolor ⊢
  left; swap; right
  all_goals {
    intros w w_elem_A insw v v_elem_A insv vnw
    have := scolor w w_elem_A insw _ _ insv vnw
    first | exact C'.adj_sub this | unfold C' at this; simp [C'.induce_adj] at this; exact this w_elem_A v_elem_A
  }

-- We prove some properties of the Ramsey property that will come in handy:

-- The Ramsey property is symmetric in `m` and `n`.
@[simp] lemma ramseyProp_symm {N m n : ℕ} : (ramseyProp N m n) ↔ (ramseyProp N n m) := by
  have (V : Type) [dV : DecidableEq V] (p : SimpleGraph V → Prop) :
    (∀ (C : SimpleGraph V) [DecidableRel C.Adj], p C) ↔ ∀ (C : SimpleGraph V) [DecidableRel C.Adj], p Cᶜ :=
    ⟨fun a C d ↦ a Cᶜ, fun a C d ↦ by rw [← compl_compl C]; exact a Cᶜ⟩

  simp_rw [ramseyProp]
  constructor
  all_goals {
    intro h v a b c
    rw [this]
    intro C d
    simp_rw [isNIndepSet_compl, ← isNIndepSet_compl Cᶜ, compl_compl]
    exact (exists_congr (fun _ => Or.comm)).mp (h v c C)
  }

-- The Ramsey number is also symmetric.
@[simp] lemma R_symm {m n : ℕ} : R m n = R n m := by simp[R]

-- The Ramsey number, if it exists, is positive if both `m` and `n` are positive.
lemma R_pos (m n : ℕ) (mpos : 0 < m) (npos : 0 < n) (nen : {N | ramseyProp N m n}.Nonempty) :
    0 < R m n := by
  simp_rw [R]
  by_contra R0; push_neg at R0
  apply eq_zero_of_le_zero at R0
  have : ramseyProp 0 m n := by have := sInf_mem nen; rw [← R0]; exact this
  simp_rw [ramseyProp, isNIndepSet_iff, isNClique_iff] at this
  obtain ⟨s, p⟩ := this (Fin 0) rfl (⊥ : SimpleGraph (Fin 0))
  simp_rw [eq_zero_of_le_zero (card_finset_fin_le s)] at p
  cases p <;> simp_all


----------------------------------------------------------------------------------------------------
-- the thing

--     "Now, suppose R(m −1, n) and R(m, n −1) exist.
--     We then prove that R(m, n) exists and that
--     R(m, n) ≤R(m −1, n) + R(m, n −1)."
-- We need to prove for positive `m, n`, since the inequality does not hold for `m, n = 0`:
-- `R(0,m) = 0`, `R(1,m) = 1` but `R(1,1) = 1 > 0 = 0 + 0 = R(0,1) + R(1,0)`
-- We shift everything by 1 compared to the book so we won't have to deal with subtraction on ℕ.
-- We don't show the actual inequality because that follows directly from the definition of the infimum.
-- instead we only show existence by providing a representative
theorem R_bounded_recursive (m n : ℕ) (posₘ : 0 < m) (posₙ : 0 < n)
    (rₘ : ∃ N, ramseyProp N (m + 1) n)
    (rₙ : ∃ N, ramseyProp N m (n + 1)) :
    ramseyProp (R m (n + 1) + R (m + 1) n) (m + 1) (n + 1) := by
  -- "Suppose `N = R(m − 1, n) + R(m, n − 1)`...", but shift by 1
  set N := R m (n + 1) + R (m + 1) n with Neq

  -- "...and consider an arbitrary red-blue coloring of K_N."
  intro V _ _ cardV C _

  -- We need to ensure we're not talking about the empty graph here, so we can pick a vertex.
  have V_nonempty : Nonempty V := by
    rw [← card_pos_iff, cardV]
    exact add_pos (R_pos m (n+1) posₘ (zero_lt_succ n) rₙ) (R_pos (m+1) n (zero_lt_succ m) posₙ rₘ)

  -- " For a vertex `v`, let `A` be the set of vertices joined to `v`
  --   by a red edge, and `B` the vertices joined by a blue edge."
  let v : V := V_nonempty.some
  let A := Cᶜ.neighborFinset v

  -- "We find that either `|A| ≥ R(m − 1, n)` or `|B| ≥ R(m, n − 1)`." (shift by 1, again)
  wlog R_le_cardA : R m (n + 1) ≤ #A with h
  · -- The case `|B| ≥ R m (n - 1)` is indeed analogous, but this is a bit involved to prove.
    let B := C.neighborFinset v
    have R_le_cardB : R n (m + 1) ≤ #B := by
      have := Nat.eq_add_of_sub_eq (le_sub_one_of_lt (degree_lt_card_verts C v)) (degree_compl C v).symm
      have := calc (R m (n + 1) + R n (m + 1)) - 1
              _ = #A + #B := by rw [@R_symm n, ← Neq, ← cardV, card_neighborFinset_eq_degree]; exact this
              _ < R m (n + 1) + #B := by simp [lt_of_not_le R_le_cardA]
      exact le_of_add_le_add_left (le_of_pred_lt this)

    -- We reduce this case to symmetry, so we apply the appropriate rewrites.
    have ex m n := Exists.imp (fun N => (@ramseyProp_symm N m n).mp)
    apply ex at rₘ; apply ex at rₙ
    rw [Neq, @R_symm m, @R_symm (m + 1), add_comm] at cardV

    -- TODO there is some trouble with inferring the complete type here.
    have : #B = Cᶜᶜ.degree v := by simp [B]; congr!; exact (compl_compl C).symm
    rw [this] at R_le_cardB

    -- This case is symmetric if we consider the complement graph. We obtain a monochromatic
    -- vertex subset of the complement graph and show that it's monochromatic with the other color
    -- in `C`.
    -- `h` is the wlog hypothesis
    simp only [forall_const, Nonempty.forall] at h
    obtain ⟨s, rs⟩ := h n m posₙ posₘ rₙ rₘ V cardV Cᶜ v R_le_cardB

    simp_rw [isNIndepSet_compl, ← isNIndepSet_compl Cᶜ, compl_compl] at rs
    exact ⟨s, rs.symm⟩

  · --"Suppose `|A| ≥ R(m − 1, n)`." (shifted by 1)
    have A_all_red : ∀ {u}, u ∈ A → ¬ C.Adj v u := by
      intro u a
      simp_all only [mem_neighborFinset, compl_adj, not_false_eq_true, A, v]

    --    "Then by the definition of `R(m − 1, n)`, there either exists in `A` a
    --     subset `A_R` of size `m − 1` all of whose edges are colored red which together
    --     with `v` yields a red `K_m`, or there is a subset `A_B` of size n with all edges
    --     colored blue."

    -- `|A| ≥ R m (n + 1)`, so the coloring it induces also has the Ramsey property according to
    -- the induction hypothesis.
    let ramsey_inducedA := clear (R m (n + 1)) #A R_le_cardA (sInf_mem rₙ) A (card_coe A)

    -- Hence, there exists a monochromatic subset of `A`. We call it `Aₘ`.
    let ⟨Aₘ, monochrom⟩ := @ramsey_inducedA (inducedColoring C A).coe (Classical.decRel (inducedColoring C A).coe.Adj)

    -- `Aₘ` is a subset of the induced graph's vertices `A`, so it's a Finset `{ x // x ∈ A }`.
    -- We need to embed it into `V` to talk about corresponding vertices in the big graph `C`
    let embedFinset : A ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    set AₘV : Finset V := (Finset.map embedFinset Aₘ) with AVe

    have AₘV_subset_A : AₘV ⊆ A := by
      intro _ memAV
      simp_all [AₘV, A, embedFinset]
      exact memAV.1

    -- We consider the two cases:
    -- `AₘV` has size `m` with all edges colored red, which together with `v` yields a red `K_(m+1)`
    -- `AₘV` has size `n + 1` with all edges colored blue
    cases' monochrom with all_red all_blue
    · rw [isNIndepSet_iff] at all_red
      -- case one: `Aₘ` is all red and of size `m`.
      -- the candidate set: `AₘV` together with `v`
      let Aᵥ := insert v AₘV

      have elem_A {x : V} (xnv : v ≠ x) (x_elem_Aᵥ : x ∈ Aᵥ) : x ∈ A := by
        cases' mem_insert.mp x_elem_Aᵥ with xeqv x_elem_AV
        · exact (xnv xeqv.symm).elim
        · exact AₘV_subset_A x_elem_AV

      -- It indeed describes an all-red subgraph of `C`:
      have C_red : C.IsIndepSet Aᵥ := by
        rw [isIndepSet_iff, Set.Pairwise]
        -- We show pairwise redness of some `u, w ∈ Aᵥ`.
        intro u u_elem_Aᵥ w w_elem_Aᵥ unw

        -- We need to handle the case that `u` or `w` happen to be `v`.
        by_cases uvw : (u = v) ∨ (w = v)
        · -- if one of the vertices is `v`, the edge is red by the definition of `A`.
          cases' uvw with eq eq
          all_goals subst eq
          · exact A_all_red (elem_A (ne_of_eq_of_ne rfl unw) w_elem_Aᵥ)
          · exact fun a => (A_all_red (elem_A (ne_of_eq_of_ne rfl unw.symm) u_elem_Aᵥ)) a.symm
        · -- the interesting case: two members of `Aᵥ` that are not `v` have a red edge
          -- we project them to `A`
          push_neg at uvw
          obtain ⟨wₐ, ⟨wₐelem_Aₘ, cw⟩⟩ := mem_map.mp (Finset.mem_of_mem_insert_of_ne w_elem_Aᵥ uvw.right)
          obtain ⟨uₐ, ⟨uₐelem_Aₘ, cu⟩⟩ := mem_map.mp (Finset.mem_of_mem_insert_of_ne u_elem_Aᵥ uvw.left)
          rw [← cw, ← cu] at unw ⊢

          -- the projections of the vertices are red in the induced coloring
          have : ¬(inducedColoring C A).coe.Adj wₐ uₐ :=
            all_red.1 wₐelem_Aₘ uₐelem_Aₘ (by intro a; subst a cu; exact unw rfl)

          simp only [Subgraph.coe_adj, Subgraph.induce_adj, Subtype.coe_prop, true_and] at this
          exact fun a => this (C.adj_symm a)

      -- It remains to show the size of `Aᵥ` is `m+1`.
      refine ⟨Aᵥ, (Or.inl ⟨C_red, ?_⟩)⟩

      have : v ∉ AₘV := fun a => (not_mem_neighborFinset_self Cᶜ v) (AₘV_subset_A a)
      simp_all only [not_false_eq_true, card_insert_of_not_mem, card_map, Aᵥ, AₘV]


    · -- if `Aₘ` is all blue and of size `n + 1`, we're done.
      rw [isNClique_iff, (card_map embedFinset).symm] at all_blue

      have : C.IsClique AₘV := by
        simp [AVe, coe_map]
        exact C.induce_isClique all_blue.1

      refine ⟨AₘV, Or.inr ⟨this, all_blue.2⟩⟩


----------------------------------------------------------------------------------------------------
-- my induction principle
-- we recurse on a binary predicate `P : (m n : ℕ) → 2 ≤ m → 2 ≤ n → Prop`
-- with fixed lower bounds `2` on `m` and `2` on `n`
-- we have two base cases `∀ n, P 2 n` and `∀ m, P m 2`
-- the inductive step goes from `P (m+1) n` and ` P m (n+1)` to `P (m + 1) (n + 1)`
lemma two_le_orth_induction {P : ∀ m n, 2 ≤ m → 2 ≤ n → Prop}
    (baseₙ : ∀ m leₘ,       P m 2 leₘ (AtLeastTwo.prop))
    (baseₘ : ∀ n leₙ,       P 2 n (AtLeastTwo.prop) leₙ)
    (succ  : ∀ m n leₘ leₙ, P (m + 1) n (le_succ_of_le leₘ) leₙ →
                            P m (n + 1) leₘ (le_succ_of_le leₙ) →
                            P (m + 1) (n + 1) (le_succ_of_le leₘ) (le_succ_of_le leₙ)) :
    ∀ m n leₘ leₙ, P m n leₘ leₙ
    | 0, _, le₀, _                   => (two_ne_zero (eq_zero_of_le_zero le₀)).elim
    | _, 0, _, le₀                   => (two_ne_zero (eq_zero_of_le_zero le₀)).elim
    | m + 1, n + 1, le_sucₘ, le_sucₙ => by
        cases' le_sucₘ with _ leₘ
        · exact (baseₘ _ _)
        · cases' le_sucₙ with _ leₙ
          · exact (baseₙ _ _)
          · have Pₘ := two_le_orth_induction baseₙ baseₘ succ (m + 1) n (le_succ_of_le leₘ) leₙ
            have Pₙ := two_le_orth_induction baseₙ baseₘ succ m (n + 1) leₘ (le_succ_of_le leₙ)
            exact (succ m n _ _ Pₘ Pₙ)


----------------------------------------------------------------------------------------------------
-- Base case proofs

-- "As a start, we certainly have `R(m, 2) = m` because either all of the edges
-- of `K_m` are red or there is a blue edge, resulting in a blue `K_2`. By symmetry,
-- we have `R(2, n) = n`."
-- The paper proof omits explicitly stating the actual induction base cases, which are
-- `∀ m, R(m, 2) ≤ R(m-1, 2) + R(m, 1)` and `∀ n, R(2, n) ≤ R(1, n) + R(2, n-1)`
-- so we also need to know the values of `R(m, 1)` and `R(1, n)`.

-- We prove that `K_m` has the `(m, 2)` Ramsey property.
lemma ramseyProp_two {m : ℕ} : ramseyProp m m 2 := by
    intro V finV decV cardV C _
    let all : Finset V := univ
    by_cases all_red : C.IsNIndepSet m all
    · -- All edges are red, so we're done
      exact ⟨all, (Or.inr all_red).symm⟩
    · -- There is a blue edge
      rw [isNIndepSet_iff, isIndepSet_iff, Set.Pairwise] at all_red
      rw [not_and_or, card_univ] at all_red
      simp [cardV] at all_red
      obtain ⟨v, ⟨_, ⟨w, ⟨_, ⟨_, vwblue⟩⟩⟩⟩⟩ := all_red
      let s : Finset V := {v, w}
      have pairblue : C.IsNClique 2 s := by simp_all [isNClique_iff, s]
      exact ⟨s, (Or.inl pairblue).symm⟩

-- That suffices as a base case for the existence proof.
theorem exists_N_ramseyProp {m n : ℕ} (leₘ : 2 ≤ m) (leₙ : 2 ≤ n) : (∃ N, ramseyProp N m n) := by
  induction' m, n, leₘ, leₙ using two_le_orth_induction with m _ n _ m n leₘ leₙ rₘ rₙ
  · exact ⟨m, ramseyProp_two⟩
  · simp; exact ⟨n, ramseyProp_two⟩
  · have := R_bounded_recursive m n (zero_lt_of_lt leₘ) (zero_lt_of_lt leₙ) rₘ rₙ
    exact ⟨(R m (n + 1) + R (m + 1) n), this⟩


-- The base case follows by proving `m` is minimal.
lemma R_two {m : ℕ} : R m 2 = m := by
  have m_le_N (N : ℕ) (ram : ramseyProp N m 2) : m ≤ N := by
    obtain ⟨s, h⟩ := ram (Fin N) (Fintype.card_fin N) ⊥
    have : ¬ (IsNClique ⊥ 2 s) := by
      rw [isNClique_bot_iff]
      push_neg
      intro si
      simp [one_lt_two] at si
    simp[this] at h
    rw [← h.2]
    exact (card_finset_fin_le s)
  exact le_antisymm (Nat.sInf_le ramseyProp_two) (le_csInf ⟨m, ramseyProp_two⟩ m_le_N)

----------------------------------------------------------------------------------------------------
-- The binomial bounds

theorem R_bounded_choose (m n : ℕ) (m1 : 2 ≤ m) (n1 : 2 ≤ n) : R m n ≤ (m + n - 2).choose (m - 1) := by
  -- we use the same induction principle as before.
  induction' m, n, m1, n1 using two_le_orth_induction with m rₘ n _ m n leₘ leₙ rₘ rₙ
  · simp [R_two]
    have := Nat.le_of_eq (choose_succ_left m m (zero_lt_of_lt rₘ))
    simp at this
    assumption
  · simp [R_two]
  · -- The actual bound from the book.
    have bound : R (m + 1) (n + 1) ≤ R m (n + 1) + R (m + 1) n :=
      Nat.sInf_le (R_bounded_recursive m n (zero_lt_of_lt leₘ) (zero_lt_of_lt leₙ)
                             (exists_N_ramseyProp (le_add_right_of_le leₘ) leₙ)
                             (exists_N_ramseyProp leₘ (le_add_right_of_le leₙ)))

    have : m + (n + 1) - 2 + 1 = m + 1 + (n + 1) - 2 := by rw [add_comm, add_comm m 1, add_assoc,
                                                               ← Nat.add_sub_assoc (le_add_right_of_le leₘ)]

    calc R (m + 1) (n + 1) ≤ R m (n + 1) + R (m + 1) n                                     := by exact bound
                         _ ≤ R m (n + 1)  + (m + 1 + n - 2).choose (m + 1 - 1)             := by simp; simp [R_symm] at rₘ; exact rₘ
                         _ ≤ (m + (n + 1) - 2).choose (m - 1) + (m + 1 + n - 2).choose m   := by simp[rₙ]
                         _ = (m + (n + 1) - 2).choose (m - 1) + (m + (n + 1) - 2).choose m := by simp[add_assoc, add_comm n 1]
                         _ = (m + (n + 1) - 2 + 1).choose m                                := (choose_succ_left (m+(n+1)-2) m (zero_lt_of_lt leₘ)).symm
                         _ = (m + 1 + (n + 1) - 2).choose (m + 1 - 1)                      := by simp only [this, add_tsub_cancel_right]

-- what other people call the ramsey number
noncomputable abbrev Rr (k : ℕ) := R k k

lemma R_bounded_pow_two {k : ℕ} : Rr (k + 2) ≤ 2 ^ (2 * k + 1) := by
  calc R (k+2) (k+2) ≤ (k + 2 + (k + 2) - 2).choose (k + 2 - 1) := by exact (R_bounded_choose (k+2) (k+2) (le_add_left 2 k) (le_add_left 2 k))
                   _ = (2 * (k + 2) - 2).choose (k + 1)         := by simp_all only [Nat.add_one_sub_one, ← two_mul]
                   _ ≤ 2 ^ (2 * k + 1)                          := choose_succ_le_two_pow
