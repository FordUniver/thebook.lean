import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Card
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
-- converting between finsets of fin A and fin N with A ≤ N

section EmbedFinset

variable {A N : ℕ} (h : A ≤ N) (Aa: Finset (Fin A))

def embed_finset : Finset (Fin N) := map (castLEEmb h) Aa

lemma embed_card : #(embed_finset h Aa) = #Aa := by rw[embed_finset, card_map]

lemma embed_neq : ∀ a b : Fin A, a ≠ b ↔ (castLEEmb h a) ≠ (castLEEmb h b) := by
  intros; simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

lemma embed_mem : ∀ w, w ∈ embed_finset h Aa → ∃ ww , ww ∈ Aa ∧ w = castLEEmb h ww := by
  intros w a
  simp_all only [embed_finset, mem_map, castLEEmb_apply, castLE_rfl, id_eq]
  obtain ⟨w_1, ⟨_, right⟩⟩ := a
  subst right
  simp_all only [castLE_inj, exists_eq_right']

lemma embed_mem' : b ∈ Aa → castLE h b ∈ embed_finset h Aa := by
  intro binA
  simp only [embed_finset, mem_map, castLEEmb_apply, castLE_inj, exists_eq_right]
  exact binA

end EmbedFinset

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

-- abbrev SimpleGraph.selfSubgraph (G : SimpleGraph V) := SimpleGraph.toSubgraph G (fun ⦃_ _⦄ a => a)

-- -- def embed (A : Finset (Fin N)) (_: a ∈ A) : Fin N := (castLEEmb (Nat.le_refl N)).toFun a

--  -- TODO these should be induced subgraphs but idk how
-- def inducedColoring (A : Finset (Fin N)) (C : EdgeColoring N) (h : #A ≤ N) :
--     ∃ I : EdgeColoring #A, (∀ v w, (I.red v w) ↔ (C.red (castLEEmb h v) (castLEEmb h w))) := by
--   have sI := SimpleGraph.Subgraph.induce C.selfSubgraph A
--   have : sI.verts = A := by sorry --simp [Subgraph.induce]
--   have : #(sI.verts) = #A := by sorry --simp [Subgraph.induce]
--   subst this
--   refine ⟨sI.coe, ?_⟩


 -- TODO these should be induced subgraphs but idk how
def inducedColoring (A : Finset (Fin N)) (G : EdgeColoring N) : EdgeColoring #A := by
  have h : #A ≤ N := card_finset_fin_le A
  exact {
    Adj := fun v w => G.Adj (castLEEmb h v) (castLEEmb h w),
    symm := by rw[Adj]; exact fun ⦃x y⦄ a => adj_symm G a,
    loopless := by rw[Adj]
                   simp_all only [castLEEmb_apply]
                   exact fun v => id (G.loopless (castLEEmb h v))
  }

lemma induceColor {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)) (h : #A ≤ N):
    ∀ v w, (inducedColoring A C).red v w ↔ C.red (castLEEmb h v) (castLEEmb h w) := by
  intro v w
  simp_all only [castLEEmb_apply]
  rfl

lemma induceColorb {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)) (h : #A ≤ N) (v w : Fin #A):
    (inducedColoring A C).blue v w ↔ C.blue (castLEEmb h v) (castLEEmb h w) := by
  simp_all only [castLEEmb_apply]
  rfl

lemma induce_blue {C : EdgeColoring N} {A : Finset (Fin N)} {h : #A ≤ N} {Aa : Finset (Fin #A)} :
    blue Aa (inducedColoring A C) ↔ blue (embed_finset h Aa) C := by
    apply Iff.intro
    · rw [blue, Set.Pairwise] at *
      intro a b c d e f
      simp_all only [mem_coe, ne_eq, castLEEmb_apply]
      obtain ⟨x, ⟨xm, xl⟩⟩ := embed_mem h Aa b c
      obtain ⟨y, ⟨ym, yl⟩⟩ := embed_mem h Aa d e
      subst xl yl
      exact a xm ym ((embed_neq h x y).mpr f)

    · rw [blue, Set.Pairwise] at *
      intro a b c d e f
      rw [induceColorb]
      simp_all only [mem_coe, ne_eq, castLEEmb_apply]
      exact a (embed_mem' h Aa c) (embed_mem' h Aa e) (by simp[embed_neq, f])

lemma induce_red {C : EdgeColoring N} {A : Finset (Fin N)} {h : #A ≤ N} {Aa : Finset (Fin #A)} :
    red Aa (inducedColoring A C) ↔ red (embed_finset h Aa) C := by
    apply Iff.intro
    · rw [red, Set.Pairwise] at *
      intro a b c d e f
      simp_all only [mem_coe, ne_eq, castLEEmb_apply]
      obtain ⟨x, ⟨xm, xl⟩⟩ := embed_mem h Aa b c
      obtain ⟨y, ⟨ym, yl⟩⟩ := embed_mem h Aa d e
      subst xl yl
      exact a xm ym ((embed_neq h x y).mpr f)

    · rw [red, Set.Pairwise] at *
      intro a b c d e f
      rw [induceColor]
      simp_all only [mem_coe, ne_eq, castLEEmb_apply]
      exact a (embed_mem' h Aa c) (embed_mem' h Aa e) (by simp[embed_neq, f])

----------------------------------------------------------------------------------------------------
-- ramsey property

def ramseyProp (N m n : ℕ) :=
    ∀ (C : EdgeColoring N), ∃ (s : Finset (Fin N)), (red s C ∧ s.card = m) ∨ (blue s C ∧ s.card = n)

lemma clear (s : ℕ) (Nles : N ≤ s) : ramseyProp N m n → ramseyProp s m n := by
  intros Nleqs C
  rw [ramseyProp] at *
  have eq := embed_card Nles (univ : Finset (Fin N))
  simp at eq
  let i := (inducedColoring (embed_finset Nles (univ : Finset (Fin N))) C)
  rw [eq] at i
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
  symm


----------------------------------------------------------------------------------------------------
-- ramsey number

noncomputable def R (m n : ℕ) : ℕ := sInf { N | ramseyProp N m n}

@[simp] lemma RSymm {m n : ℕ} : R m n = R n m := by simp[R]

lemma Rramsey (nen : {N | ramseyProp N m n}.Nonempty) : ramseyProp (R m n) m n := Nat.sInf_mem nen

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
  · obtain ⟨mN, ⟨mNramsey, mNbound⟩⟩ := mr
    obtain ⟨nN, ⟨nNramsey, nNbound⟩⟩ := nr
    let N := R m (n + 1) + R (m + 1) n
    use N

    have nz : 0 < N := by sorry
    have v : Fin N := by sorry

    simp_all only [Nat.add_one_sub_one]

    have : ramseyProp N (m + 1) (n + 1) := by
      intro C

      let B := C.neighborFinset v
      let A := Cᶜ.neighborFinset v

      have a_card_or_b_card : R (m-1) n ≤ #A ∨ R m (n-1) ≤ #B := by sorry

      wlog RleqA : (R m (n + 1)) ≤ #A with h -- this is so cool
      · sorry
      · -- A also has the Ramsey property: There exists a subset of A that is all red or blue.
        -- using the induction hypothesis!
        let ⟨Aa, p⟩ := (clear #A RleqA (Rramsey (Set.nonempty_of_mem nNramsey))) (inducedColoring A C)

        -- all vertices in A have a red edge with v
        have Avred : ∀ u ∈ A, C.red v u := by aesop

        -- idk how to embed Aa to Fin N
        have cardAleN : #A ≤ N := card_finset_fin_le A
        let AN : Finset (Fin N) := embed_finset cardAleN Aa

        wlog allRed : red Aa (inducedColoring A C) ∧ #Aa = m
        · simp[allRed] at p
          refine ⟨AN, Or.inr ⟨induce_blue.mp p.1 ,?_ ⟩⟩
          · have : #Aa = #AN := (embed_card cardAleN Aa).symm
            rw[this] at p
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
                subst weqv; have : u ∈ A := sorry; exact fun a => Avred u this (adj_symm C a)
              · have winAN : w ∈ AN := Finset.mem_of_mem_insert_of_ne winc (fun a => weqv (symm a))
                unfold_let AN at winAN
                obtain ⟨ww, ⟨wwAa, cw⟩⟩ := embed_mem cardAleN Aa w winAN
                obtain ⟨uu, ⟨uuAa, cu⟩⟩ := embed_mem cardAleN Aa u uinAN
                rw [cw, cu] at unw
                have := Aared wwAa uuAa ((embed_neq cardAleN ww uu).mpr unw.symm)
                have := (induceColor C A cardAleN ww uu).mp this
                rw [← cw, ← cu] at this
                exact fun a => this (adj_symm C a)

          have vnmemAN : v ∉ AN := sorry
          have : #c = m+1 := by calc #c
            _ = #AN + 1 := card_insert_of_not_mem vnmemAN
            _ = #(embed_finset cardAleN Aa) + 1 := rfl
            _ = #Aa + 1  := by simp[embed_card]
            _ = m + 1 := by simp[Aacard]

          exact Exists.intro c (Or.inl ⟨cred, this⟩)


    exact ⟨this, Nat.sInf_le this⟩

    
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
