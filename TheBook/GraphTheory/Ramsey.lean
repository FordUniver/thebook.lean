import Mathlib.Combinatorics.SimpleGraph.Clique
import TheBook.ToMathlib.IndependentSet
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

open SimpleGraph Finset Fintype Nat

-- mathlib?
lemma Nat.sInf_le_sInf {A B : Set ℕ} (nea : A.Nonempty) (subs : A ⊆ B) : sInf B ≤ sInf A := by
  by_contra infle
  exact infle (Nat.sInf_le (Set.mem_of_subset_of_mem subs (sInf_mem nea)))

-- this is probably in mathlib somewhere?
lemma neighbor_card_sum [Fintype V] [Nonempty V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V = (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card + 1 := by
  have disj : Disjoint (neighborFinset G v) (neighborFinset Gᶜ v) := by
    simp only [neighborFinset_def, Set.disjoint_toFinset, compl_neighborSet_disjoint]
  simp only [← card_union_of_disjoint disj]
  simp only [neighborFinset_def, ← Set.toFinset_union, card_neighborSet_union_compl_neighborSet]
  exact (sub_one_add_one Fintype.card_ne_zero).symm

----------------------------------------------------------------------------------------------------
-- edge colorings

-- abbrev SimpleGraph.red (C : SimpleGraph V) (v w : V) := ¬ C.Adj v w
-- abbrev SimpleGraph.blue (C : SimpleGraph V) (v w : V) := C.Adj v w

def red (s : Finset V) (C : SimpleGraph V) := (s.toSet).Pairwise (fun v w => ¬ C.Adj v w)
def blue (s : Finset V) (C : SimpleGraph V) := (s.toSet).Pairwise C.Adj


@[simp] lemma red_compl (s : Finset V) (C : SimpleGraph V) : red s Cᶜ ↔ blue s C := by
  simp_rw [red, blue, compl_adj, Set.Pairwise]
  simp_all only [ne_eq, not_false_eq_true, true_and, not_not]

@[simp] lemma blue_compl (s : Finset V) (C : SimpleGraph V) : blue s Cᶜ ↔ red s C := by
  simp[red, blue, isIndependentSet_iff_isClique_of_complement]

----------------------------------------------------------------------------------------------------
-- edge colorings induced by vertex subsets

abbrev SimpleGraph.selfSubgraph (G : SimpleGraph V) := SimpleGraph.toSubgraph G (fun ⦃_ _⦄ a => a)

abbrev inducedColoring (G : SimpleGraph V) (A : Finset V) := G.selfSubgraph.induce A.toSet

def embedFinset : (A : Finset α) ↪ α := {
          toFun := fun a : { x // x ∈ A } => a.1
          inj' := Subtype.val_injective
        }

noncomputable def embedFintype (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α ≤ Fintype.card β) :
    α ↪ β := Trunc.out (Function.Embedding.truncOfCardLE h)

lemma induce_blue {C : SimpleGraph V} {A : Finset V} {Aᵥ : Finset A}:
    blue Aᵥ (inducedColoring C A).coe ↔ blue (map embedFinset Aᵥ) C := by
  simp_rw [blue, Set.Pairwise, inducedColoring]
  simp only [ne_eq, Subgraph.coe_adj, Subgraph.induce_adj, Subtype.coe_prop, true_and,
    Subtype.forall, Subtype.mk.injEq, coe_map, Set.mem_image, forall_exists_index, and_imp]
  apply Iff.intro
  · intro Cadj a b binA bAᵥ eba x y yinA yAᵥ exy bny
    subst eba exy
    exact Cadj (embedFinset ⟨b, binA⟩) binA bAᵥ (embedFinset ⟨y, yinA⟩) yinA yAᵥ bny
  · intro Cadj a ainA aAᵥ b binA bAᵥ anb
    exact Cadj a ainA aAᵥ rfl b binA bAᵥ rfl anb

----------------------------------------------------------------------------------------------------
-- ramsey property

-- TODO the type signatures are verbose. can i somehow define a type that's in all the classes i want
-- but still have inference work?
-- this should do it:
-- class MeFinClass (type : Type*) (N : outParam Nat) extends Fintype type where
--   [toDecidableEq : DecidableEq type]
--   [fin : Fintype type]
--   card : Fintype.card type = N
def ramseyProp (N m n : ℕ) := ∀ (V : Type) [Fintype V] [DecidableEq V] (_ : Fintype.card V = N),
    ∀ (C : SimpleGraph V) [DecidableRel C.Adj], ∃ s, (red s C ∧ s.card = m) ∨ (blue s C ∧ s.card = n)

lemma clear (N s : ℕ) (h : N ≤ s) : ramseyProp N m n → ramseyProp s m n := by
  intros ramN W _ _ Wcard C _
  rw [ramseyProp] at *
  rw [← Wcard, ← Fintype.card_fin N] at h
  let A : Finset W := Finset.map (embedFintype (Fin N) W h) Finset.univ
  let C' := C.selfSubgraph.induce A.toSet
  have : A.card = N := by simp only [embedFintype, card_map, card_univ, Fintype.card_fin, A]
  have := ramN A (by simp [this, Fintype.card_coe])
  obtain ⟨s, red_or_blue⟩ :=  @this C'.coe (Classical.decRel C'.coe.Adj)
  rcases red_or_blue with ⟨scolor, scard⟩ | ⟨scolor, scard⟩
  all_goals use (Finset.map embedFinset s)
  all_goals simp [scard, red, blue, Set.Pairwise] at scolor ⊢
  left; swap; right
  all_goals intros w winW winA insw embw v vinW vinA insv embv vnw
  all_goals have := scolor winW winA insw vinW vinA insv (by subst embv embw; simpa)
  all_goals subst embv embw
  · exact C'.adj_sub this
  · unfold C' at this
    simp [C'.induce_adj] at this
    exact this winA vinA

lemma ramsey_iff (N m n : ℕ) : (ramseyProp N m n) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (_: Fintype.card V = N) (C : SimpleGraph V) [DecidableRel C.Adj],
    ∃ (s : Finset V), (C.IsNIndependentSet m s) ∨ (C.IsNClique n s) := by
  simp_rw [isNClique_iff, isNIndependentSet_iff, isClique_iff, isIndependentSet_iff, ramseyProp, red, blue]

@[simp] lemma ramseySymm : (ramseyProp N m n) ↔ (ramseyProp N n m) := by
  have (V : Type) [dV : DecidableEq V] (p : SimpleGraph V → Prop) :
    (∀ (C : SimpleGraph V) [DecidableRel C.Adj], p C) ↔ ∀ (C : SimpleGraph V) [DecidableRel C.Adj], p Cᶜ :=
    ⟨fun a C d ↦ a Cᶜ, fun a C d ↦ by rw [← compl_compl C]; exact a Cᶜ⟩

  simp_rw [ramsey_iff N]
  constructor
  all_goals {
    intro h v a b c
    rw [this]
    intro C d
    simp [isNIndependentSet_iff_isNClique_of_complement]
    simp [← isNIndependentSet_iff_isNClique_of_complement]
    exact (exists_congr (fun _ => Or.comm)).mp (h v c C)
  }

----------------------------------------------------------------------------------------------------
-- ramsey number

noncomputable def R (m n : ℕ) : ℕ := sInf { N | ramseyProp N m n}

@[simp] lemma RSymm {m n : ℕ} : R m n = R n m := by simp[R]

lemma Rramsey (nen : {N | ramseyProp N m n}.Nonempty) : ramseyProp (R m n) m n := sInf_mem nen

lemma Rpos (m n : ℕ) (mpos : 0 < m) (npos : 0 < n) (nen : {N | ramseyProp N m n}.Nonempty) :
    0 < R m n := by
  simp_rw [R]
  by_contra R0; push_neg at R0
  apply eq_zero_of_le_zero at R0
  have : ramseyProp 0 m n := by have := sInf_mem nen; rw [← R0]; exact this
  rw [ramseyProp] at this
  obtain ⟨s, p⟩ := this (Fin 0) rfl (⊥ : SimpleGraph (Fin 0))
  simp_rw [eq_zero_of_le_zero (card_finset_fin_le s)] at p
  match p with
  | Or.inl ⟨_, p⟩ => exact mpos.ne p
  | Or.inr ⟨_, p⟩ => exact npos.ne p

----------------------------------------------------------------------------------------------------
-- base case proofs

lemma ramsey2 : ramseyProp m m 2 := by
    intro V finV decV cardV C _
    let all : Finset V := univ
    by_cases allRed : red all C
    · have : all.card = m := by simp only [card_univ, cardV, all]
      exact Exists.intro all (Or.symm (Or.inr (And.intro allRed this)))
    · rw [red, Set.Pairwise] at allRed
      push_neg at allRed
      obtain ⟨v, ⟨_, ⟨w, ⟨_, ⟨_, vwblue⟩⟩⟩⟩⟩ := allRed
      let s : Finset V := {v, w}
      have pairblue : blue s C := by simp_all [blue, s]
      exact Exists.intro s (Or.symm (Or.inl (And.intro pairblue (card_pair (Adj.ne vwblue)))))

lemma m_leq_R (nge : 1 < n) (N : ℕ) (ram : ramseyProp N m n) : m ≤ N := by
  obtain ⟨s, h⟩ := ram (Fin N) (Fintype.card_fin N) ⊥
  have : ¬ (blue s ⊥ ∧ #s = n) := by
    push_neg
    simp only [blue, isClique_bot_iff]
    intro si
    exact Nat.ne_of_lt (lt_of_le_of_lt (card_le_one_iff.mpr fun {_ _} a' b' => si a' b') nge)
  simp[this, red] at h
  rw [← h.2]
  exact (card_finset_fin_le s)

lemma R2 : R m 2 = m := le_antisymm (Nat.sInf_le ramsey2) (le_csInf ⟨m, ramsey2⟩ (m_leq_R one_lt_two))

lemma ramsey1 {m : ℕ} [nz : NeZero N] : ramseyProp N m 1 := by
  intro V _ _ cardV C _
  have nenV : Nonempty V := card_pos_iff.mp (by subst cardV; exact pos_of_neZero (Fintype.card V))
  refine ⟨{nenV.some}, Or.inr ?_⟩
  simp_all [card_singleton, and_true, blue]

lemma R1 {m : ℕ} [nz : NeZero m] : R m 1 = 1 := by
  refine le_antisymm (Nat.sInf_le ramsey1) ?_
  by_contra h
  simp [R] at h
  cases h with
  | inl ram0m1 => obtain ⟨_, sl⟩ := ram0m1 (Fin 0) rfl ⊥
                  simp [eq_empty_of_isEmpty] at sl
                  exact nz.out.symm sl.2
  | inr h_2 => exact (Set.mem_empty_iff_false m).mp (by rw [← h_2]; exact ramsey1)

----------------------------------------------------------------------------------------------------
-- my induction principle
-- we recurse on a binary predicate `P : (m n : ℕ) → bm ≤ m → bn ≤ n → Prop`
-- with fixed lower bounds `bm` on `m` and `bn` on `n`
-- we have two base cases `∀ n, P bm n` and `∀ m, P m bn`
-- the inductive step goes from `P (m+1) n` and ` P m (n+1)` to `P (m + 1) (n + 1)`

lemma le_induction2 {bm bn : ℕ} {P : ∀ m n, bm ≤ m → bn ≤ n → Prop}
    (basem : ∀ n hbn,       P bm n bm.le_refl hbn)
    (basen : ∀ m hbm,       P m bn hbm bn.le_refl)
    (succ  : ∀ m n hbm hbn, P (m + 1) n (le_succ_of_le hbm) hbn →
                            P m (n + 1) hbm (le_succ_of_le hbn) →
                            P (m + 1) (n + 1) (le_succ_of_le hbm) (le_succ_of_le hbn)) :
    ∀ m n hbm hbn, P m n hbm hbn
  | 0, _, b, _        => eq_zero_of_le_zero b ▸ (basem _ _)
  | _, 0, _, b        => eq_zero_of_le_zero b ▸ (basen _ _)
  | m + 1, n + 1, hbm, hbn =>
    (le_succ_iff.1 hbm).by_cases
      (fun h : bm ≤ m ↦ (le_succ_iff.1 hbn).by_cases
        (fun hh : bn ≤ n ↦ by
          have rem := le_induction2 basem basen succ (m+1) n hbm hh
          have ren := le_induction2 basem basen succ m (n+1) h hbn
          exact (succ m n h hh rem ren)
        )
        (fun hh : bn = n + 1 ↦ hh ▸ (basen _ _)))
      (fun h : bm = m + 1 ↦ h ▸ (basem _ _))

----------------------------------------------------------------------------------------------------
-- the thing
-- le_induction because the inequality does not hold for `m/n = 0`:
-- `R(0,m) = 0`, `R(1,m) = 1` but `R(1,1) = 1 > 0 = 0+0 = R(0,1)+R(1,0)`

theorem recRbound : (m n : ℕ) → 2 ≤ m → 2 ≤ n →
    ∃ N, ramseyProp N m n ∧
    (R m n) ≤ R (m - 1) n + R m (n - 1) := by

  have base (m : ℕ) [NeZero m] : R 2 m ≤ R (2 - 1) m + R 2 (m - 1) := by
    simp [R2, R1]
    match m with
    | 0 => exact le_add_left 0 1
    | m + 1 => simp [Nat.add_one_sub_one, add_comm]

  intro m n ml1 nl1
  induction' m, n, ml1, nl1 using le_induction2 with m mr n nr m n mg2 ng2 mr nr
  · exact Exists.intro m ⟨ramseySymm.mp ramsey2, @base m ⟨not_eq_zero_of_lt mr⟩⟩
  · exact Exists.intro n ⟨ramsey2, by simp only [add_comm, RSymm] at base; exact @base n ⟨not_eq_zero_of_lt nr⟩⟩
  · let ⟨mN, ⟨mNramsey, mNbound⟩⟩ := mr
    let ⟨nN, ⟨nNramsey, nNbound⟩⟩ := nr

    simp_all only [Nat.add_one_sub_one, and_true]

    set N := R m (n + 1) + R (m + 1) n with Neq

    have nz : N ≠ 0 := not_eq_zero_of_lt (add_pos
                        (Rpos m (n+1) (zero_lt_of_lt mg2) (zero_lt_succ n) (Set.nonempty_def.mpr ⟨nN, nNramsey⟩))
                        (Rpos (m+1) n (zero_lt_succ m) (zero_lt_of_lt ng2) (Set.nonempty_def.mpr ⟨mN, mNramsey⟩)))

    have ramseyN : ramseyProp N (m + 1) (n + 1) := by
      intro V _ _ cardV C _

      have nenV : Nonempty V := card_pos_iff.mp (by rw [cardV]; exact zero_lt_of_ne_zero nz)
      let v : V := nenV.some

      -- all vertices joined to v with a red edge
      let A := Cᶜ.neighborFinset v

      wlog RleqA : R m (n + 1) ≤ Cᶜ.degree v with h
      · have bge : R n (m + 1) ≤ @degree _ Cᶜᶜ v -- TODO inference of implicit arguments does not work properly
            (@neighborSetFintype _ Cᶜᶜ _ (fun a b => @Compl.adjDecidable _ Cᶜ (Classical.decRel Cᶜ.Adj) _ a b) v) := by
          push_neg at RleqA
          have := calc (R m (n + 1)) + (R n (m + 1))
                  _ = C.degree v + Cᶜ.degree v + 1 := by rw [@RSymm n, ← Neq, ← cardV]; exact neighbor_card_sum C
                  _ < C.degree v + R m (n + 1) + 1 := by simp [RleqA]
                  _ = R m (n + 1) + C.degree v + 1 := by simp [add_comm]
                  _ = R m (n + 1) + Cᶜᶜ.degree v + 1 := by congr!; simp [compl_compl] -- compl implicitly changes adjDecidable instance so we need congr
          convert le_of_lt_succ (lt_of_add_lt_add_left this) -- we need convert to arrive at the desired adjDecidable instance

        simp only [forall_const, Nonempty.forall] at h

        rw [Neq] at *
        repeat rw [@RSymm m, @RSymm (m + 1)] at *

        -- TODO this is a large thing. can i use wlog hypothesis without so much noise?
        -- this case is symmetric if we consider the complement graph.
        obtain ⟨s, rs⟩ := @h n m nN mN base ng2 mg2 ⟨nN, ramseySymm.mp nNramsey⟩ ⟨mN, ramseySymm.mp mNramsey⟩
                                (ramseySymm.mp nNramsey)
                                (by rw [@RSymm (m - 1), add_comm _ (R n m)] at nNbound; assumption)
                                (ramseySymm.mp mNramsey)
                                (by rw [add_comm (R n m)] at mNbound; assumption)
                                (by rw [add_comm] at nz; assumption) (by rw [add_comm] at Neq; assumption)
                                _ _ (by rw [add_comm] at cardV; assumption) Cᶜ (Classical.decRel Cᶜ.Adj) v bge

        simp_rw [red_compl, blue_compl] at rs
        exact ⟨s, rs.symm⟩

      · -- all vertices in A have a red edge with v
        have Avred : ∀ {u}, u ∈ A → ¬ C.Adj v u := by
          intro u a
          simp_all only [mem_neighborFinset, compl_adj, not_false_eq_true, A, v]

        -- A has cardinality ≥ R m (n + 1), so it also has the ramsey property according to the induction hypothesis.
        -- we name its monochromatic subset Aᵥ
        let ramA := clear (R m (n + 1)) #A RleqA (Rramsey (Set.nonempty_of_mem nNramsey)) A (card_coe A)
        let ⟨Aᵥ, monochrom⟩ := @ramA (inducedColoring C A).coe (Classical.decRel (inducedColoring C A).coe.Adj)

        -- Aᵥ is a subset of the induced graph's vertices A, so it's a Finset { x // x ∈ A }
        -- we need to embed it into V to talk about corresponding vertices in the big graph C
        let AᵥV : Finset V := (Finset.map embedFinset Aᵥ)

        have AVsubA : AᵥV ⊆ A := by
          intro _ memAV
          simp_all [AᵥV, A, embedFinset]
          exact memAV.1

        cases' monochrom with allRed allBlue
        · -- the candidate set: Aᵥ together with v
          let c := insert v AᵥV

          have inA {x : V} (xnv : v ≠ x) (xinc : x ∈ c) : x ∈ A := by
            cases' mem_insert.mp xinc with xeqv xinAV
            · exact (xnv xeqv.symm).elim
            · exact AVsubA xinAV

          -- it indeed describes an all-red subgraph:
          have cred : red c C := by
            -- we show pairwise redness of some u, w ∈ c
            intro u uinc w winc unw

            -- we need to handle the case that some edge partners are v
            by_cases uvw : (u = v) ∨ (w = v)
            · cases' uvw with eq eq
              all_goals subst eq
              · exact Avred (inA (ne_of_eq_of_ne rfl unw) winc)
              · exact fun a => (Avred (inA (ne_of_eq_of_ne rfl unw.symm) uinc)) a.symm
            · -- the interesting case: two members of c that are not v have a red edge
              -- we project them to A
              push_neg at uvw
              obtain ⟨wₐ, ⟨wₐinAᵥ, cw⟩⟩ := mem_map.mp (Finset.mem_of_mem_insert_of_ne winc uvw.right)
              obtain ⟨uₐ, ⟨uₐinAᵥ, cu⟩⟩ := mem_map.mp (Finset.mem_of_mem_insert_of_ne uinc uvw.left)
              rw [← cw, ← cu] at unw ⊢

              -- the projections of the vertices are red in the induced coloring
              have : ¬(inducedColoring C A).coe.Adj wₐ uₐ :=
                allRed.1 wₐinAᵥ uₐinAᵥ (by intro a; subst a cu; exact unw rfl)

              simp only [Subgraph.coe_adj, Subgraph.induce_adj, Subtype.coe_prop, true_and] at this
              exact fun a => this (adj_symm C a)

          refine Exists.intro c (Or.inl ⟨cred, ?_⟩)

          have : v ∉ AᵥV := fun a => (not_mem_neighborFinset_self Cᶜ v) (AVsubA a)
          simp_all only [not_false_eq_true, card_insert_of_not_mem, card_map, c, AᵥV]
        · -- if Aᵥ is all blue, we're done.
          rw [(card_map embedFinset).symm] at allBlue
          refine ⟨AᵥV, Or.inr ⟨induce_blue.mp allBlue.1, allBlue.2⟩⟩

    exact ⟨N, ⟨ramseyN, Nat.sInf_le ramseyN⟩⟩

----------------------------------------------------------------------------------------------------

theorem chooseRbound (m n : ℕ) (m1 : 2 ≤ m) (n1 : 2 ≤ n) : R m n ≤ choose (m + n - 2) (m - 1) := by
  induction' m, n, m1, n1 using le_induction2 with m mr n nr m n mg2 ng2 mr nr
  · simp [R2]
  · simp [R2]
    have := choose_succ_left n n (zero_lt_of_lt nr)
    simp at this
    exact Nat.le_of_eq this
  · let ⟨_, ⟨_, lee⟩⟩ := recRbound (m+1) (n+1) (le_add_right_of_le mg2) (le_add_right_of_le ng2)
    have : m + (n + 1) - 2 + 1 = m + 1 + (n + 1) - 2 := by rw [add_comm, add_comm m 1, add_assoc,
                                                               ← Nat.add_sub_assoc (le_add_right_of_le mg2)]

    calc R (m + 1) (n + 1) ≤ R m (n + 1) + R n (m + 1)                                     := by simp at lee; exact lee
                         _ ≤ R m (n + 1)  + choose (m + 1 + n - 2) (m + 1 - 1)             := by simp; simp [RSymm] at mr; exact mr
                         _ ≤ choose (m + (n + 1) - 2) (m - 1) + choose (m + 1 + n - 2) m   := by simp[nr]
                         _ = choose (m + (n + 1) - 2) (m - 1) + choose (m + (n + 1) - 2) m := by simp[add_assoc, add_comm n 1]
                         _ = choose (m + (n + 1) - 2 + 1) m                                := (choose_succ_left (m+(n+1)-2) m (zero_lt_of_lt mg2)).symm
                         _ = choose (m + 1 + (n + 1) - 2) (m + 1 - 1)                      := by simp only [this, add_tsub_cancel_right]

-- what other people call the ramsey number
noncomputable abbrev Rr (k : ℕ) := R k k

lemma powRbound : Rr (k + 2) ≤ 2 ^ (2 * k + 1) := by
  have : {k, k + 1} ⊆ range (2 * k + 1 + 1) := by
    rw [insert_subset_iff, singleton_subset_iff, two_mul]
    simp; constructor
    · rw [add_assoc]; rw [add_assoc]; exact Nat.lt_add_of_pos_right (zero_lt_succ (k + 1))
    · rw [add_assoc]; exact Nat.lt_add_of_pos_right (zero_lt_succ k)

  calc R (k+2) (k+2) ≤ (k + 2 + (k + 2) - 2).choose (k + 2 - 1)          := by exact chooseRbound (k+2) (k+2) (Nat.le_add_left 2 k) (Nat.le_add_left 2 k)
           _ = choose (2 * (k + 2) - 2) (k + 1)                          := by simp_all only [Nat.add_one_sub_one, ← two_mul]
           _ = (2 * k + 2 - 1).choose k + (2 * k + 2 - 1).choose (k + 1) := Nat.choose_succ_right (2 * k + 2) k (zero_lt_succ (2 * k + 1))
           _ = ∑ m ∈ {k, k + 1}, (2 * k + 1).choose m                    := (Finset.sum_pair (ne_add_one k)).symm
           _ ≤ ∑ m ∈ range ((2 * k + 1) + 1), (2 * k + 1).choose m       := sum_le_sum_of_subset this
           _ = 2 ^ (2 * k + 1)                                           := Nat.sum_range_choose _
