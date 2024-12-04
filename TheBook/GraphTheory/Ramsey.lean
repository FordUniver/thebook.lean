import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Maps
import TheBook.ToMathlib.IndependentSet
import Mathlib.Tactic.Linarith

open SimpleGraph Finset Fintype Fin Nat

-- mathlib!
lemma Nat.sInf_le_sInf {A B : Set ℕ} (nea : A.Nonempty) (subs : A ⊆ B) : sInf B ≤ sInf A := by
  by_contra infle
  exact infle (Nat.sInf_le (Set.mem_of_subset_of_mem subs (Nat.sInf_mem nea)))

-- should be clear, no?! probably missing some import or other
instance SimpleGraph.Finite.adjDecidable
  {V : Type u} [inst : Fintype V] [inst : DecidableEq V] (G : SimpleGraph V) : DecidableRel G.Adj := by sorry


-- this is probably in mathlib somewhere?
lemma neighbor_card_sum [nz : NeZero N] (G : SimpleGraph (Fin N)) :
    N = (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card + 1 := by
  have disj : Disjoint (neighborFinset G v) (neighborFinset Gᶜ v) := by
    simp only [neighborFinset_def, Set.disjoint_toFinset, compl_neighborSet_disjoint]
  simp only [← card_union_of_disjoint disj]
  simp only [neighborFinset_def, ← Set.toFinset_union, card_neighborSet_union_compl_neighborSet]
  rw [Fintype.card_fin]
  simp[Nat.sub_one_add_one nz.ne]

----------------------------------------------------------------------------------------------------
-- edge colorings

abbrev EdgeColoring N := SimpleGraph (Fin N)

abbrev EdgeColoring.red (C : EdgeColoring N) (v w : Fin N) := ¬ C.Adj v w
abbrev EdgeColoring.blue (C : EdgeColoring N) (v w : Fin N) := C.Adj v w

def red (s : Finset (Fin N)) (C : EdgeColoring N) := (s.toSet).Pairwise C.red
def blue (s : Finset (Fin N)) (C : EdgeColoring N) := (s.toSet).Pairwise C.blue

@[simp] lemma red_compl (s : Finset (Fin N)) (C : EdgeColoring N) : red s Cᶜ ↔ blue s C := by
  simp[red, blue, isIndependentSet_iff_isClique_of_complement]

@[simp] lemma blue_compl (s : Finset (Fin N)) (C : EdgeColoring N) : blue s Cᶜ ↔ red s C := by
  simp[red, blue, isIndependentSet_iff_isClique_of_complement]

----------------------------------------------------------------------------------------------------
-- edge colorings induced by vertex subsets

abbrev SimpleGraph.selfSubgraph (G : SimpleGraph V) := SimpleGraph.toSubgraph G (fun ⦃_ _⦄ a => a)

structure inducedSubgraph (A : Finset (Fin N)) (C : EdgeColoring N) where
  graph : EdgeColoring #A
  colorEmbed : (Fin #A) ↪ A
  adjEmbed : ∀ v w, graph.blue v w ↔ C.blue (colorEmbed v) (colorEmbed w)

-- problem with using subgraph: C.induce A is a SimpleGraph A, but to apply ramsey we need a SimpleGraph (Fin #A)
-- so either we rewrite everything for some type MyFin N that's any finite type with N elements, or we tediously
-- translate the SimpleGraph A into a SimpleGraph #A at which point we might just as well use our own subgraph...
-- noncomputable def inducedColoring2 (A : Finset (Fin N)) (C : EdgeColoring N) : inducedSubgraph A C := by
--   let Alist := A.toList
--   have alist_len := length_toList A
--   have {a} : a ∈ Alist → a ∈ A := fun am => mem_toList.mp am
--   let colorEmbed : (Fin #A) ↪ A := {
--     toFun := fun a => ⟨Alist.get ((congrArg Fin alist_len.symm).mp a),
--                        this sorry⟩
--     inj' := sorry
--   }
--   let subgraph := C.selfSubgraph.induce A
--   exact {
--     graph := subgraph.coe
--     colorEmbed := colorEmbed
--     adjEmbed := fun v w => by simp_all only [graph]
--   }

noncomputable def inducedColoring (A : Finset (Fin N)) (C : EdgeColoring N) : inducedSubgraph A C := by
  let Alist := A.toList -- can we avoid this? i don't like choice
  have alist_len := length_toList A
  have {a} : a ∈ Alist → a ∈ A := fun am => mem_toList.mp am

  let colorEmbed : (Fin #A) ↪ A := {
    toFun := fun a => by
      let a' := (congrArg Fin alist_len.symm).mp a
      exact ⟨Alist.get a', this (Alist.get_mem a' a'.isLt)⟩
    inj' := fun a b c => by
      simp_all only [eq_mp_eq_cast, Subtype.mk.injEq]
      have := (List.Nodup.get_inj_iff A.nodup_toList).mp c
      simp_all only [_root_.cast_inj]
  }

  exact {
    graph := {
      Adj := fun v w => C.Adj (colorEmbed v) (colorEmbed w),
      symm := by rw[Adj]; exact fun ⦃x y⦄ a => adj_symm C a,
      loopless := by rw[Adj, Irreflexive]; intro a; exact SimpleGraph.irrefl C
    }
    colorEmbed := colorEmbed
    adjEmbed := by simp only [implies_true]
  }

lemma induceColor {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)) : let C' := (inducedColoring A C);
    ∀ v w, C'.graph.red v w ↔ C.red (C'.colorEmbed v) (C'.colorEmbed w) := by
  intro v _ _
  simp_all only [v]
  rfl

lemma induceColorb {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)) (v w : Fin #A) : let C' := (inducedColoring A C);
    (inducedColoring A C).graph.blue v w ↔ C.blue (C'.colorEmbed v) (C'.colorEmbed w) := by
  rfl

lemma neEmbed {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)) : let C' := (inducedColoring A C);
   ∀ v w, (C'.colorEmbed v) ≠ (C'.colorEmbed w) ↔ v ≠ w := by
  intros
  simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq]


----------------------------------------------------------------------------------------------------
-- ramsey property

def ramseyProp (N m n : ℕ) :=
    ∀ (C : EdgeColoring N), ∃ (s : Finset (Fin N)), (red s C ∧ s.card = m) ∨ (blue s C ∧ s.card = n)

lemma clear (s : ℕ) (Nles : N ≤ s) : ramseyProp N m n → ramseyProp s m n := by
  intros Nleqs C
  rw [ramseyProp] at *
  -- have eq := embed_card Nles (univ : Finset (Fin N))
  -- simp at eq
  -- let i := (inducedColoring (sorry Nles (univ : Finset (Fin N))) C)
  -- rw [eq] at i
  sorry

lemma ramsey_iff (N m n : ℕ) : (ramseyProp N m n) ↔
    ∀ (C : EdgeColoring N), ∃ (s : Finset (Fin N)), (C.IsNIndependentSet m s) ∨ (C.IsNClique n s) := by
  simp_rw [isNClique_iff, isNIndependentSet_iff, ramseyProp, red, blue]

@[simp] lemma ramseySymm : (ramseyProp N m n) ↔ (ramseyProp N n m) := by
  repeat rw [ramsey_iff]
  have (p : EdgeColoring N → Prop) : (∀ (C : EdgeColoring N), p C) ↔ ∀ (C : EdgeColoring N), p Cᶜ :=
    ⟨fun a C ↦ a Cᶜ ,fun a C ↦ by rw [← compl_compl C]; exact a Cᶜ ⟩
  rw [this]
  simp [isNIndependentSet_iff_isNClique_of_complement]
  simp [← isNIndependentSet_iff_isNClique_of_complement]
  simp [Or.comm]

----------------------------------------------------------------------------------------------------
-- ramsey number

noncomputable def R (m n : ℕ) : ℕ := sInf { N | ramseyProp N m n}

@[simp] lemma RSymm {m n : ℕ} : R m n = R n m := by simp[R]

lemma Rramsey (nen : {N | ramseyProp N m n}.Nonempty) : ramseyProp (R m n) m n := Nat.sInf_mem nen

lemma Rpos (m n : ℕ) (mpos : 0 < m) (npos : 0 < n) (nen : {N | ramseyProp N m n}.Nonempty) :
    0 < R m n := by
  simp_rw [R]
  by_contra R0
  push_neg at R0
  apply eq_zero_of_le_zero at R0
  have : ramseyProp 0 m n := by have := sInf_mem nen; rw [← R0]; exact this
  rw[ramseyProp] at this
  have := this ⊥
  obtain ⟨s, p⟩ := this
  have : #s = 0 := eq_zero_of_le_zero (card_finset_fin_le s)
  simp_rw [this] at p
  match p with
  | Or.inl ⟨_, p⟩ => exact mpos.ne p
  | Or.inr ⟨_, p⟩ => exact npos.ne p

----------------------------------------------------------------------------------------------------
-- base case proofs

lemma mem : m ∈ { N | ramseyProp N m 2} := by
    simp [ramseyProp]
    intro C
    let all : Finset (Fin m) := univ
    by_cases allRed : all.toSet.Pairwise C.red
    · have : all.card = m := by simp only [card_univ, Fintype.card_fin, all]
      exact Exists.intro all (Or.symm (Or.inr (And.intro allRed this)))
    · rw [Set.Pairwise] at allRed
      push_neg at allRed
      obtain ⟨v, ⟨_, ⟨w, ⟨_, ⟨_, vwblue⟩⟩⟩⟩⟩ := allRed
      let s : Finset (Fin m) := {v, w}
      have pairblue : s.toSet.Pairwise C.blue := by simp_all [s]
      exact Exists.intro s (Or.symm (Or.inl (And.intro pairblue (card_pair (Adj.ne (Decidable.not_not.mp vwblue))))))


lemma m_leq_R (nge : 1 < n) : ∀ N ∈ {N | ramseyProp N m n}, m ≤ N := by
  intro N r
  obtain ⟨s, h⟩ := r ⊥

  have : ¬ (blue s ⊥ ∧ #s = n) := by
    have hm {s : Finset (Fin N)} (sub : (s : Set (Fin N)).Subsingleton) : s.card ≤ 1 := by
      have := Set.Subsingleton.eq_empty_or_singleton sub
      aesop
    push_neg
    simp only [blue, isClique_bot_iff]
    exact fun si => Nat.ne_of_lt (by calc #s ≤ 1 := by exact (hm si)
                                           _ < n := by exact nge)
  simp[this, red] at h
  obtain ⟨a , b⟩ := h
  subst b
  exact card_finset_fin_le s

lemma twor : R m 2 = m :=
  le_antisymm (Nat.sInf_le mem) (le_csInf ⟨m, mem⟩ (m_leq_R one_lt_two))

lemma twol : R 2 n = n := by
  rw [R]
  simp [ramseySymm]
  exact twor

lemma mem1 {m : ℕ} [NeZero m] : m ∈ { N | ramseyProp N m 1} := by
  simp [ramseyProp]
  intro C
  refine ⟨{(0 : Fin m)}, Or.inr ?_⟩
  simp_all [card_singleton, and_true, blue]

lemma mem11 {m : ℕ} [NeZero m] : 1 ∈ { N | ramseyProp N m 1} := by
  simp [ramseyProp]
  intro C
  refine ⟨{(0 : Fin 1)}, Or.inr ?_⟩
  simp_all [card_singleton, and_true, blue]

lemma onel {m : ℕ} [nz : NeZero m] : 0 < R m 1 := by
  by_contra h
  simp [R] at h
  cases h with
  | inl h_1 => obtain ⟨s, sl⟩ := h_1 ⊥
               simp [eq_empty_of_isEmpty] at sl
               exact nz.out.symm sl.2
  | inr h_2 => have mm : m ∈ {N | ramseyProp N m 1} := mem1
               simp_all only [mem1, ne_eq, Set.mem_empty_iff_false]

lemma oner {m : ℕ} [nz : NeZero m] : R m 1 = 1 := le_antisymm (Nat.sInf_le mem11) (@onel m nz)


----------------------------------------------------------------------------------------------------
-- my induction principle
-- we recurse on a binary predicate `P` and have two base cases `∀ n, P bm n` and `∀ m, P bn`

lemma le_induction2 {bm bn : ℕ} {P : ∀ m n, bm ≤ m → bn ≤ n → Prop}
    (basem : ∀ n hbn, P bm n bm.le_refl hbn)
    (basen : ∀ m hbm, P m bn hbm bn.le_refl)
    (succ : ∀ m n hbm hbn, P (m+1) n (Nat.le_succ_of_le hbm) hbn →
                           P m (n+1) hbm (Nat.le_succ_of_le hbn) →
                           P (m + 1) (n + 1) (Nat.le_succ_of_le hbm) (Nat.le_succ_of_le hbn)) :
    ∀ m n hbm hbn, P m n hbm hbn
  | 0, mm, hbm, hbn => Nat.eq_zero_of_le_zero hbm ▸ (basem _ _)
  | m, 0, hbm, hbn => Nat.eq_zero_of_le_zero hbn ▸ (basen _ _)
  | m + 1, n + 1, hbm, hbn =>
    (Nat.le_succ_iff.1 hbm).by_cases
      (fun h : bm ≤ m ↦ (Nat.le_succ_iff.1 hbn).by_cases
        (fun hh : bn ≤ n ↦ by
         have rem := le_induction2 basem basen succ (m+1) n hbm hh
         have ren := le_induction2 basem basen succ m (n+1) h hbn
         exact (succ m n h hh rem ren)
        )
        (fun hh : bn = n + 1 ↦ hh ▸ (basen _ _)))
      (fun h : bm = m + 1 ↦ h ▸ (basem _ _))


----------------------------------------------------------------------------------------------------
-- the thing
-- le_induction because the inequality does not hold for m/n=0:
-- R(0,m)=0, R(1,m)=1 but R(1,1)=1>0=0+0-=R(0,1)+R(1,0)

theorem rammm1 : (m n : ℕ) → 2 ≤ m → 2 ≤ n →
    ∃ N, ramseyProp N m n ∧
    (R m n) ≤ R (m - 1) n + R m (n - 1) := by

  have base (m : ℕ) [NeZero m] : R 2 m ≤ R (2 - 1) m + R 2 (m - 1) := by
    simp [twor, oner]
    match m with
    | 0 => exact le_add_left 0 1
    | m + 1 => simp [Nat.add_one_sub_one, add_comm]

  intro m n ml1 nl1
  induction' m, n, ml1, nl1 using le_induction2 with m mr n nr m n mg2 ng2 mr nr
  · exact Exists.intro m ⟨ramseySymm.mp mem , @base m ⟨not_eq_zero_of_lt mr⟩⟩
  · exact Exists.intro n ⟨mem , by simp only [add_comm, RSymm] at base; exact @base n ⟨not_eq_zero_of_lt nr⟩⟩
  · let ⟨mN, ⟨mNramsey, mNbound⟩⟩ := mr
    let ⟨nN, ⟨nNramsey, nNbound⟩⟩ := nr

    simp_all only [Nat.add_one_sub_one]


    have (N : ℕ) (v : Fin N) (nz : 0 < N) (Neq : N = R m (n + 1) + R (m + 1) n) :
        ramseyProp N (m + 1) (n + 1) := by
      intro C

      let B := C.neighborFinset v
      let A := Cᶜ.neighborFinset v
      have Beq : B = C.neighborFinset v := by ext a : 1; simp_all only [B, mem_neighborFinset] -- what is it i don't understand about let statements

      wlog RleqA : (R m (n + 1)) ≤ #A with h -- this is so cool
      · have bge : R n (m + 1) ≤ #B := by
          push_neg at RleqA
          unfold_let A B at *

          have : NeZero N := NeZero.of_pos nz
          have := calc (R m (n + 1)) + (R n (m + 1)) = N := by rw [@RSymm n (m + 1), ← Neq]
                  _ = #(C.neighborFinset v) + #(Cᶜ.neighborFinset v) + 1 := neighbor_card_sum C
                  _ < #(C.neighborFinset v) + R m (n + 1) + 1 := by sorry --simp [RleqA]
                  _ = R m (n + 1) + #(C.neighborFinset v) + 1 := by simp [add_comm]
          exact Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_left this)

        rw [@RSymm (m + 1) n, @RSymm (m + 1) (n - 1), @RSymm m n, add_comm (R n m)] at mNbound
        rw [@RSymm m (n + 1), @RSymm (m - 1) (n + 1), @RSymm m n, add_comm _ (R n m)] at nNbound
        rw [@RSymm m (n + 1), @RSymm (m + 1) n, add_comm] at Neq

        apply ramseySymm.mp at nNramsey
        apply ramseySymm.mp at mNramsey
        -- wtf
        have bgee : R n (m + 1) ≤ #(@neighborFinset (Fin N) Cᶜᶜ v (@neighborSetFintype (Fin N) Cᶜᶜ (Fin.fintype N) (fun a b => @Compl.adjDecidable (Fin N) Cᶜ (fun a b => Finite.adjDecidable Cᶜ a b) (instDecidableEqFin N) a b) v)) := sorry

        let ⟨s, rs⟩ := h 1 1 n m nN mN base ng2 mg2 ⟨nN, ⟨nNramsey, trivial⟩⟩
                                              ⟨mN, ⟨mNramsey, trivial⟩⟩
                                              nNramsey nNbound mNramsey mNbound N v nz Neq Cᶜ
                                              (by ext a : 1; simp_all only [B, mem_neighborFinset])
                                              bgee

        simp_rw [red_compl, blue_compl] at rs
        exact ⟨s, Or.symm rs⟩

      · -- A also has the Ramsey property: There exists a subset of A that is all red or blue.
        -- using the induction hypothesis!
        let Ca := (inducedColoring A C)
        let ⟨Aa, p⟩ := (clear #A RleqA (Rramsey (Set.nonempty_of_mem nNramsey))) Ca.graph

        -- all vertices in A have a red edge with v
        have Avred : ∀ u ∈ A, C.red v u := by aesop

        -- idk how to embed Aa to Fin N
        have cardAleN : #A ≤ N := card_finset_fin_le A

        let ANa : Finset A := (map Ca.colorEmbed Aa)
        let AN : Finset (Fin N) := map {
          toFun := fun a => a.1
          inj' := Subtype.val_injective
        } ANa

        have aEmbed : ∀ x ∈ AN, ∃ xa ∈ Aa, x = Ca.colorEmbed xa := by
          intro x a
          simp_all only [mem_map, exists_exists_and_eq_and, AN, ANa]
          obtain ⟨w_2, ⟨left, right⟩⟩ := a
          subst right
          use w_2
          constructor
          · exact left
          · exact rfl

        have ANsubsA : AN ⊆ A := by
          intro _ xAN
          simp_all [AN, A]
          exact xAN.1

        wlog allRed : red Aa Ca.graph ∧ #Aa = m
        · simp[allRed] at p
          refine ⟨AN, Or.inr ⟨?_, ?_⟩⟩
          · rw [blue, Set.Pairwise]
            rw [blue, Set.Pairwise] at p
            intros x xAN y yAN xny
            obtain ⟨xaaa, ⟨xaa, xa⟩⟩ := aEmbed x xAN
            obtain ⟨yaaa, ⟨yaa, ya⟩⟩ := aEmbed y yAN
            rw [xa, ya]
            rw [xa, ya] at xny
            simp [← Ca.adjEmbed]
            exact p.1 xaa yaa ((neEmbed C A xaaa yaaa).mp (fun a => xny (congrArg Subtype.val a)))
          · have : #Aa = #AN := by simp [AN, ANa]
            rw [this] at p
            exact p.2
        · obtain ⟨ Aared, Aacard ⟩ := allRed

          let c := insert v AN

          have cred : red c C := by
            intro u uinc w winc unw
            by_cases ueqv : u = v -- can i have nicer nested cases please
            · by_cases weqv : w = v
              · -- both are v so they cannot have a red edge
                subst weqv; subst ueqv; exact (unw rfl).elim
              · sorry -- symmetric to below...
            · have uinAN : u ∈ AN := Finset.mem_of_mem_insert_of_ne uinc ueqv
              by_cases weqv : v = w
              · -- all edges containing v are red
                subst weqv
                have : u ∈ A := ANsubsA uinAN
                exact fun a => Avred u this (adj_symm C a)
              · have winAN : w ∈ AN := Finset.mem_of_mem_insert_of_ne winc (fun a => weqv (symm a))
                unfold_let AN at winAN
                obtain ⟨ww, ⟨wwAa, cw⟩⟩ := aEmbed w winAN
                obtain ⟨uu, ⟨uuAa, cu⟩⟩ := aEmbed u uinAN
                simp_rw [cw, cu, Ca] at unw
                have := Aared wwAa uuAa ((neEmbed C A ww uu).mp
                  (fun a => unw (congrArg Subtype.val a.symm)))
                have cr : ∀ v w, Ca.graph.red v w ↔ C.red (Ca.colorEmbed v) (Ca.colorEmbed w) := by
                    intros
                    rfl
                have := (cr ww uu).mp this
                rw [← cw, ← cu] at this
                exact fun a => this (adj_symm C a)

          have vnmemAN : v ∉ AN := fun a => (not_mem_neighborFinset_self Cᶜ v) (ANsubsA a)
          have : #c = m + 1 := by simp_all only [card_insert_of_not_mem vnmemAN, card_map, AN, ANa, Aacard]

          exact Exists.intro c (Or.inl ⟨cred, this⟩)


    let N := R m (n + 1) + R (m + 1) n
    have mNpos : 0 < R (m + 1) n := Rpos (m+1) n (zero_lt_succ m) (zero_lt_of_lt ng2) (Set.nonempty_def.mpr ⟨mN, mNramsey⟩)
    have nNpos : 0 < R m (n + 1) := Rpos m (n+1) (zero_lt_of_lt mg2) (zero_lt_succ n) (Set.nonempty_def.mpr ⟨nN, nNramsey⟩)

    have nz : NeZero N := { out := by unfold N; exact not_eq_zero_of_lt (add_pos nNpos mNpos) }

    have NRam := this N (0 : Fin N) (pos_of_neZero N) rfl
    simp only [Nat.add_one_sub_one, exists_and_right]

    exact And.intro ⟨N, NRam⟩ (Nat.sInf_le NRam)

----------------------------------------------------------------------------------------------------


lemma foo {P : ℕ → Prop} (n : ℕ) : (_ : ∀ n, P n) → (_ : 0 < n) → P (n - 1) := by
  intro x x_1
  simp_all only

lemma reeeec (nr : 0 < n) : choose m (n - 1) + choose m n = choose (m + 1) n := by
  have := (choose_succ_succ' m (n - 1)).symm
  simp only[Nat.sub_add_cancel (zero_lt_of_lt nr)] at this
  exact this

theorem ram2 : (m n : ℕ) → (m1 : 2 ≤ m) → (n1 : 2 ≤ n) → R m n ≤ Nat.choose (m + n - 2) (m - 1) := by
  intro m n ml1 nl1
  induction' m, n, ml1, nl1 using le_induction2 with m mr n nr m n mg2 ng2 mr nr
  · simp[twor]
  · simp[twor];
    have := foo n (fun m => choose_succ_self_right m) (zero_lt_of_lt nr);
    simp only[Nat.sub_add_cancel (zero_lt_of_lt nr)] at this
    simp_all only [le_refl]

  · let ⟨_, ⟨_, lee⟩⟩ := rammm1 (m+1) (n+1) (le_add_right_of_le mg2) (le_add_right_of_le ng2)

    have h1: m + 1 + n - 2 = m + (n + 1) - 2 := by sorry
    have h2: (m + (n + 1) - 2 + 1) = (m + 1 + (n + 1) - 2)  := sorry

    calc R (m + 1) (n + 1) ≤ R m (n + 1) + R n (m + 1) := by simp at lee; exact lee
                         _ ≤ R m (n + 1)  + choose (m + 1 + n - 2) (m + 1 - 1) := by simp; simp [RSymm] at mr; exact mr
                         _ ≤ choose (m + (n + 1) - 2) (m - 1) + choose (m + 1 + n - 2) m := by simp[nr]
                         _ = choose (m + (n + 1) - 2) (m - 1) + choose (m + (n + 1) - 2) m := by simp[h1]
                         _ = choose (m + (n + 1) - 2 + 1) m := @reeeec m (m + (n + 1) - 2) (zero_lt_of_lt mg2)
                         _ = choose (m + 1 + (n + 1) - 2) (m + 1 - 1) := by simp_all only [h2, add_tsub_cancel_right]


noncomputable abbrev Rr (k : ℕ) := R k k

theorem ram3 {k} (_ : 2 ≤ k) : 2 ^ (k / 2) ≤ Rr k := sorry
