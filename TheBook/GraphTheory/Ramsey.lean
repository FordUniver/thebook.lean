import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Maps
import TheBook.ToMathlib.IndependentSet

open SimpleGraph Finset Fintype Fin

variable (s : Set V)

abbrev EdgeColoring N := SimpleGraph (Fin N)

-- should be clear, no?!
instance SimpleGraph.Finite.adjDecidable
  {V : Type u} [inst : Fintype V] [inst : DecidableEq V] (G : SimpleGraph V) : DecidableRel G.Adj := by sorry

abbrev EdgeColoring.blue (C : EdgeColoring N) (v w : Fin N) := C.Adj v w
abbrev EdgeColoring.red (C : EdgeColoring N) (v w : Fin N) := ¬ C.Adj v w

 -- TODO these should be induced subgraphs but idk how
def inducedColoring (A : Finset (Fin N)) (G : EdgeColoring N) : EdgeColoring #A := sorry -- induce A.toSet C
def lift (_ : Fin A) : Fin N := sorry
lemma lift_neq {A N : ℕ} : ∀ a b : Fin A, a ≠ b ↔ (@lift A N a) ≠ (@lift A N b) := sorry
lemma induceColor {N : ℕ} (C : EdgeColoring N) (A : Finset (Fin N)):
    ∀ v w, (inducedColoring A C).red v w ↔ C.red (lift v) (lift w) := sorry

def red (s : Finset (Fin N)) (C : EdgeColoring N) := (s.toSet).Pairwise C.red
def blue (s : Finset (Fin N)) (C : EdgeColoring N) := (s.toSet).Pairwise C.blue

def ramseyProperty (N m n : ℕ) :=
    ∀ (C : EdgeColoring N), ∃ (s : Finset (Fin N)), (red s C ∧ s.card = m) ∨ (blue s C ∧ s.card = n)

lemma ramsey_iff (N m n : ℕ) : (ramseyProperty N m n) ↔
    ∀ (C : EdgeColoring N), ∃ (s : Finset (Fin N)), (C.IsNClique m s) ∨ (C.IsNIndependentSet n s) :=
  sorry

lemma clear (s : ℕ) (_ : N ≤ s) : (ramseyProperty N m n) → (ramseyProperty s m n) := by
  intros Nleqs C
  rw [ramseyProperty] at *
  let Cc := SimpleGraph.induce (@univ (Fin N) _).toSet
  sorry

lemma ramseySymm : (ramseyProperty N m n) ↔ (ramseyProperty N n m) := by
  repeat rw [ramsey_iff]
  have (p : EdgeColoring N → Prop) : (∀ (C : EdgeColoring N), p C) ↔ ∀ (C : EdgeColoring N), p Cᶜ :=
    by
    apply Iff.intro
    · intro a C
      simp_all only
    · intro a C
      have := a Cᶜ
      rw [compl_compl] at this
      exact this
  rw [this]
  simp [isNIndependentSet_iff_isNClique_of_complement]
  simp [← isNIndependentSet_iff_isNClique_of_complement]
  simp [Or.comm]

noncomputable def R (m n : ℕ) : ℕ := sInf { N | ramseyProperty N m n}

lemma Rramsey (nen : {N | ramseyProperty N m n}.Nonempty) : ramseyProperty (R m n) m n := by
  rw [R]
  exact Nat.sInf_mem nen

lemma ramseyLe (N : ℕ) : (_ : ramseyProperty N m n) → m ≤ N := sorry

-- mathlib!
lemma Nat.sInf_le_sInf {A B : Set ℕ} (nea : A.Nonempty) (subs : A ⊆ B) : sInf B ≤ sInf A := by
  by_contra infle
  exact infle (Nat.sInf_le (Set.mem_of_subset_of_mem subs (Nat.sInf_mem nea)))

lemma ramnumLe : (∃ N, ramseyProperty N m n) → m ≤ R m n := by
  intro nen
  rw [R]
  have aa : {N | ramseyProperty N m n} ⊆ {N | m ≤ N} := by simp; exact ramseyLe
  exact le_csInf nen aa

lemma mem : m ∈ { N | ramseyProperty N m 2} := by
    simp [ramseyProperty]
    intro C
    let all : Finset (Fin m) := univ
    by_cases allRed : all.toSet.Pairwise C.red
    · have : all.card = m := by simp only [card_univ, Fintype.card_fin, all]
      exact Exists.intro all (Or.symm (Or.inr (And.intro allRed this)))
    · have : ∃ (v w : Fin m), C.blue v w := sorry
      obtain ⟨v, ⟨w, vwblue⟩⟩ := this
      let s : Finset (Fin m) := {v, w}
      have pairblue : s.toSet.Pairwise C.blue := by simp_all [s]
      exact Exists.intro s (Or.symm (Or.inl (And.intro pairblue (card_pair (Adj.ne vwblue)))))

lemma twor : R m 2 = m := le_antisymm (Nat.sInf_le mem) (ramnumLe (Exists.intro m mem))

lemma twonle : R 2 n = n := by
  rw [R]
  simp [ramseySymm]
  exact twor

theorem ram1 : (m n : ℕ) →
    ∃ N, ramseyProperty N m n ∧
    (R m n) ≤ (R (m - 1) n) + (R m (n - 1))
  | m , 0 => sorry
  | 0 , n => sorry
  | (m + 1) , (n + 1) => by
    let N := (R m (n + 1)) + (R (m + 1) n)
    let ⟨mN, ⟨mNramsey, mNbound⟩⟩ := ram1 m (n + 1)

    -- have : ramseyProperty N (m + 1) n := by
    have construct monoc : ∀ C : EdgeColoring N, ∃ c, (red c C ∨ blue c C) ∧ (#c ≤ N) := by
      intro C
      let v : Fin N := sorry -- how to say "any v"

      let A := C.neighborFinset v
      let B := Cᶜ.neighborFinset v

      -- this is probably in mathlib somewhere?
      have cardAB : A.card + B.card = N - 1 := by
        have union : (A ∪ B).card = N - 1 := by
          have := C.card_neighborSet_union_compl_neighborSet v
          simp_all only [Set.toFinset_card, Fintype.card_fin, Set.toFinset_union, N, A, B]
          exact this

        have : (A ∪ B).card = A.card + B.card := by
            have : Disjoint (A) (B) := by
              have := C.compl_neighborSet_disjoint v
              simp_all only [A, B]
              sorry
            have := card_union_of_disjoint this
            simp_all only [card_neighborFinset_eq_degree, N, A, B]

        simp_all [card_union_of_disjoint]

      by_cases RleqA : (R m (n + 1)) ≤ #A
      · -- A also has the Ramsey property: There exists a subset of A that is all red or blue.
        -- using the induction hypothesis!
        let ⟨Aa, p⟩ := (clear #A RleqA (Rramsey (Set.nonempty_of_mem mNramsey))) (inducedColoring A C)

        cases p with
        | inr h => sorry -- symmetric to below
        | inl h => -- all red case
                  obtain ⟨ Aared, _ ⟩ := h

                  -- idk how to lift Aa to Fin N
                  let AN : Finset (Fin N) := {lift a | a ∈ Aa} -- { a | a ∈ Aa} how!
                  have lift_set_mem : ∀ w, w ∈ AN → ∃ ww , ww ∈ Aa ∧ lift ww = w := sorry
                  have lift_card : #AN = m := sorry
                  have vnmemAN : v ∉ AN := sorry
                  -- the lifted subset also is all red
                  have ANred : ∀ w, w ∈ AN → C.red w v := by
                    intro w winAN
                    obtain ⟨ww, ⟨wwAa, cw⟩⟩ := lift_set_mem w winAN
                    sorry

                  let c := insert v AN

                  have : red c C := by
                    intro u uinc w winc unw
                    by_cases ueqv : u = v -- can i have nicer nested cases please
                    · subst ueqv
                      by_cases weqv : w = v
                      · by_contra adjvw
                        subst weqv
                        exact unw rfl
                      · sorry -- symmetric to below...
                    · have uinAN : u ∈ AN := Finset.mem_of_mem_insert_of_ne uinc ueqv
                      by_cases weqv : w = v
                      · subst weqv
                        exact ANred u uinAN
                      · have winAN : w ∈ AN := Finset.mem_of_mem_insert_of_ne winc weqv
                        obtain ⟨ ww , ⟨wwAa, cw⟩ ⟩ := lift_set_mem w winAN
                        obtain ⟨ uu , ⟨uuAa, cu⟩ ⟩ := lift_set_mem u uinAN
                        rw [← cw, ← cu] at unw
                        have := Aared wwAa uuAa ((lift_neq ww uu).mpr unw.symm)
                        have := (induceColor C A ww uu).mp this
                        rw [cw, cu] at this
                        exact fun a => ueqv (id (Eq.symm cu))

                  refine Exists.intro c ⟨Or.inl this, ?_⟩
                  · have : #A = #c + 1 := sorry --by simp [card_insert_of_not_mem vnmemAN, lift_card]
                    rw [this] at cardAB
                    have : N = #c + #B := sorry
                    simp [this]


      · have : (R (m + 1) n) ≤ B.card := sorry -- symmetric to above...
        sorry

    have : ramseyProperty N (m + 1) (n + 1) := by intro C


    refine Exists.intro N (And.intro this ?_)





theorem ram2 (m n : ℕ) : R m n ≤ Nat.choose (m + n - 2) (m - 1) := sorry

noncomputable abbrev Rr (k : ℕ) := R k k

theorem ram3 {k} (_ : 2 ≤ k) : 2 ^ (k / 2) ≤ Rr k := sorry
