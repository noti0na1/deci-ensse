import DeciENSSE.Core.Words.Self.Bound
import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Anchored.Estimate
import DeciENSSE.Anchored.Types

/-! # Paper contract: Mortal Holes

Contract entries for the section *Mortal Holes* (`sec:mo`) and its appendix (`app:mo`),
except the size estimates in `DeciENSSE.Paper.Bounds`: separator words, the base channel,
the Π-reader, the depth of mortal holes, positive desubstitution and channel towers,
anchored compression with its exchange types, dictionaries, unary words, summaries and
columns, short mortal holes and their decision, and the short-hole theorem
(`thm:mo-decide`).

Only library results and logical packaging are used below. The separator word `u ♯ t` is
`sepWord u t` over `Option α`, with `none` as the separator. An instance of the two-word
hole problem with self events is a `SelfTwoWordInstance`; its reader `R_Π` is
`Mortal.reader` with the admissions `Self.Adm`, the rejected states `Mortal.Rej` and the
relation `Mortal.Pi`. A Π-hole of a reader is written out as in the paper: a nonempty
reader hole with a comparison whose continuation letter, at the cut `x + |w| - y`, is the
separator and whose states lie in `Π`. Positive channels are `PosChan`, their positive
condition `Pos`, derivatives `posDer`, and channel towers `posTower`; agreement with
channels is `PosAgree`. The constants of the paper are `anchoredTypeBound` (`C♯`),
`anchoredAllowance` (`A♯`), `anchoredDictionaryBound` (`G♯`), `pcolBound` (`Pcol`),
`anchoredLengthBound` (`L♯`) and `anchoredExponent` (`Ξ♯`); the bound `Lnm` is
`pumpHoleBound`. Finite sets and families of letters or blocks are lists.
-/

namespace DeciENSSE.Paper

open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.LetteredHierarchy DeciNSSE.HierarchyDepth
  DeciNSSE.BoundedDepth DeciNSSE.RejectedTail DeciNSSE.Packets DeciNSSE.Exchange
  DeciNSSE.NormalForm DeciNSSE.BoundaryPairs DeciNSSE.ElementaryBound
open DeciENSSE.Anchored DeciENSSE.Core.Words

/-- **Lemma (Comparisons of the separator word)**, `lem:mo-sep`(1).
Form: The separator word is sepWord u t over Option alpha, with none as the separator. Alphabet finiteness is not required.
-/
theorem lem_mo_sep_1 {α : Type*} (u t : Word α) (x y : ℕ) (hy : y ≤ u.length) :
    ¬ IsComp (Mortal.sepWord u t) x y :=
  fun hc => Mortal.no_pre_comparison u t hc.1 hy hc

/-- **Lemma (Comparisons of the separator word)**, `lem:mo-sep`(2).
Form: Cross comparisons are TwoWordInstance.Cross, which also records the cut bounds. Alphabet finiteness is not required.
-/
theorem lem_mo_sep_2 {α : Type*} (u t : Word α) {x e : ℕ} (hx : x ≤ u.length)
    (he : e ≤ t.length) :
    IsComp (Mortal.sepWord u t) x (u.length + 1 + e) ↔ TwoWordInstance.Cross u t x e := by
  rw [Mortal.cross_comparison_iff u t hx he]
  exact ⟨fun h => ⟨hx, he, h⟩, fun h => h.2.2⟩

/-- **Lemma (Comparisons of the separator word)**, `lem:mo-sep`(3).
Form: The comparison equivalence holds over any alphabet; finiteness is not required.
-/
theorem lem_mo_sep_3 {α : Type*} (u t : Word α) {i j : ℕ} (hij : i < j) (hj : j ≤ t.length) :
    IsComp (Mortal.sepWord u t) (u.length + 1 + i) (u.length + 1 + j) ↔ IsComp t i j := by
  rw [Self.target_comparison_iff u t (by omega) hj]
  exact ⟨fun h => ⟨h.1, hj, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- **Lemma (Comparisons of the separator word)**, `lem:mo-sep`(4).
Form: An anchored comparison is a comparison whose continuation letter, at the cut x + length w - y, is the separator; aligned cross comparisons are TwoWordInstance.Aligned. Alphabet finiteness is not required.
-/
theorem lem_mo_sep_4 {α : Type*} (u t : Word α) {x e : ℕ} (hx : x ≤ u.length)
    (he : e ≤ t.length) :
    (IsComp (Mortal.sepWord u t) x (u.length + 1 + e) ∧
      (Mortal.sepWord u t)[x + (Mortal.sepWord u t).length - (u.length + 1 + e)]? =
        some none) ↔
      TwoWordInstance.Aligned u t x e := by
  have hp : u.length < (Mortal.sepWord u t).length := by simp only [Mortal.length_sepWord]; omega
  constructor
  · rintro ⟨hc, hsep⟩
    have ha : Mortal.Anchored (Mortal.sepWord u t) u.length x (u.length + 1 + e) :=
      (anchoredAt_iff (Mortal.sepWord u t) hp).mpr ⟨hc, (Mortal.separator_unique u t _).mp hsep⟩
    exact ⟨hx, he, (Mortal.anchored_iff u t hx he).mp ha⟩
  · rintro ⟨-, -, h⟩
    obtain ⟨hc, hpos⟩ := (anchoredAt_iff (Mortal.sepWord u t) hp).mp
      ((Mortal.anchored_iff u t hx he).mpr h)
    exact ⟨hc, by rw [hpos]; exact (Mortal.separator_unique u t _).mpr rfl⟩

/-- **Lemma (The base channel)**, `lem:mo-base`.
Form: The lettered monitor of a reader is ofReader and the base channel is baseChan, whose relation is also false into the start label, which no comparison reaches; the first claim holds for every word; a Pi-hole is written out as a nonempty reader hole with an anchored comparison in Pi. Neither alphabet nor state finiteness is required.
-/
theorem lem_mo_base {Γ Q : Type*} (M : DFA Γ Q) (Adm Pi : Q → Q → Prop) (Rej : Set Q)
    (sep : Γ) :
    (∀ w : List Γ, Pos (ofReader M Adm Rej) (baseChan M Pi sep) w ↔
      ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some sep ∧
        Pi (runPrefix M w x) (runPrefix M w y)) ∧
    ∀ w : List Γ, (w ≠ [] ∧ IsReaderHole M Adm Rej w ∧
      ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some sep ∧
        Pi (runPrefix M w x) (runPrefix M w y)) ↔
      PosHole (ofReader M Adm Rej) (baseChan M Pi sep) w := by
  have h1 : ∀ w : List Γ, Pos (ofReader M Adm Rej) (baseChan M Pi sep) w ↔
      ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some sep ∧
        Pi (runPrefix M w x) (runPrefix M w y) := fun w =>
    (pos_base_iff_comparison M Adm Pi Rej sep w).trans
      (exists₂_congr fun _ _ => and_congr_right fun _ => and_comm)
  refine ⟨h1, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨hw, hh, hp⟩
    exact ⟨(isHole_ofReader_iff M Adm Rej hw).mpr hh, (h1 w).mpr hp⟩
  · rintro ⟨hh, hp⟩
    exact ⟨hh.ne_nil, (isHole_ofReader_iff M Adm Rej hh.ne_nil).mp hh, (h1 w).mp hp⟩

/-- **Lemma (The Π-reader)**, `lem:mo-pi-reader`(1).
Form: The reader is Mortal.reader on all states of RState, itself a computable definition. This item also packages the computability of the relations as a computable definition, whose values are the decision procedures Self.instDecidableAdm, Mortal.instDecidableRej and Mortal.instDecidablePi for admission, rejection and Pi.
-/
def lem_mo_pi_reader_1 {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') :
    DecidableRel (Self.Adm I) ×'
    DecidablePred (· ∈ Mortal.Rej I.toTwoWordInstance) ×'
    DecidableRel (Mortal.Pi I.toTwoWordInstance) ×'
    Fintype.card (Mortal.RState SA SB SA' SB') =
      1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
        Fintype.card SA * Fintype.card SB' :=
  ⟨Self.instDecidableAdm I, Mortal.instDecidableRej I.toTwoWordInstance,
    Mortal.instDecidablePi I.toTwoWordInstance, Mortal.card_state⟩

/-- **Lemma (The Π-reader)**, `lem:mo-pi-reader`(2).
Form: A Pi-hole is written out as a nonempty reader hole with an anchored comparison in Pi; the admissions are Self.Adm, the cross and self guards together.
-/
theorem lem_mo_pi_reader_2 {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') (w : List (Option α)) :
    (w ≠ [] ∧ IsReaderHole (Mortal.reader I.toTwoWordInstance) (Self.Adm I)
        (Mortal.Rej I.toTwoWordInstance) w ∧
      ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some none ∧
        Mortal.Pi I.toTwoWordInstance (runPrefix (Mortal.reader I.toTwoWordInstance) w x)
          (runPrefix (Mortal.reader I.toTwoWordInstance) w y)) ↔
      ∃ u t, w = Mortal.sepWord u t ∧ I.IsMortalHole u t :=
  ((lem_mo_base _ _ _ _ none).2 w).trans (Self.posHole_pi_iff I w)

/-- **Lemma (The Π-reader)**, `lem:mo-pi-reader`(3).
Form: Stated for the mortal hole (u, t) of item (2); the rejected tail is the number of letters after the first rejected cut.
-/
theorem lem_mo_pi_reader_3 {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') {u t : Word α} (h : I.IsMortalHole u t) :
    ∃ j, I.J t = some j ∧
      IsFirstRejectedPrefix (Mortal.reader I.toTwoWordInstance)
        (Mortal.Rej I.toTwoWordInstance) (Mortal.sepWord u t) (u.length + 1 + j) ∧
      (Mortal.sepWord u t).length - (u.length + 1 + j) = t.length - j := by
  obtain ⟨⟨⟨hs, -, -, -⟩, hm, j, hj, -⟩, -⟩ := (I.isMortalHole_iff u t).mp h
  have hj' : I.J t = some j := hj
  exact ⟨j, hj', Mortal.first_rejected_cut _ hs hm hj', by
    simp only [Mortal.length_sepWord]; omega⟩

/-- **Lemma (Depth of mortal holes)**, `lem:mo-depth`.
Form: The depth bound d_I is written out with the state count of the reader.
-/
theorem lem_mo_depth {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') {u t : Word α} (h : I.IsMortalHole u t) :
    depth (Mortal.sepWord u t) ≤
      2 * (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
        Fintype.card SA * Fintype.card SB') * Fintype.card SA - 1 := by
  have hd := Self.mortal_depth I h
  rwa [Mortal.card_state] at hd

/-- **Lemma (Positive desubstitution)**, `lem:mo-desub`.
Form: The expansion of v' is expand l v'; the derived monitor and channel are der and posDer. State finiteness is not required.
-/
theorem lem_mo_desub {Γ C : Type*} (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (v' : List (List Γ)) (hv : v' ≠ []) (hℓ : ∀ X ∈ v', ℓ ∉ X) :
    (Pos D P (expand ℓ v') ↔ Pos (der D ℓ) (posDer D P ℓ) v') ∧
    (PosHole D P (expand ℓ v') ↔ PosHole (der D ℓ) (posDer D P ℓ) v') :=
  ⟨(pos_der_iff D P ℓ v' hv hℓ).symm, (posHole_der_iff D P ℓ v' hv hℓ).symm⟩

/-- **Corollary (Channel towers)**, `cor:mo-tower`.
Form: The canonical hierarchy is hierOf with markers markOf, which needs an inhabited alphabet; the towers are tower and posTower, and their recursion is included; the number of states is not used.
-/
theorem cor_mo_tower {α Q : Type*} [DecidableEq α] [Inhabited α] (D0 : Lettered α Q)
    (P0 : PosChan α Q) {w : List α} (hw : w ≠ []) :
    (∀ j, tower D0 (markOf w) (j + 1) = der (tower D0 (markOf w) j) (markOf w j) ∧
      posTower D0 P0 (markOf w) (j + 1) =
        posDer (tower D0 (markOf w) j) (posTower D0 P0 (markOf w) j) (markOf w j)) ∧
    ∀ j, PosHole D0 P0 w ↔
      PosHole (tower D0 (markOf w) j) (posTower D0 P0 (markOf w) j) (hierOf w j) :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun j => (pos_hierOf_iff D0 P0 hw j).symm⟩

/-- **Theorem (Anchored compression)**, `thm:mo-anchored`.
Form: L-sharp, G-sharp and Xi-sharp are anchoredLengthBound, anchoredDictionaryBound and anchoredExponent. Alphabets are inhabited for the canonical hierarchy; finiteness of the alphabet and N at least 1 are not needed. A Pi-hole is written out as in lem:mo-base.
-/
theorem thm_mo_anchored {Γ Q α C : Type*} [DecidableEq Γ] [Inhabited Γ] [Fintype Q]
    [DecidableEq α] [Inhabited α] [Fintype C]
    (M : DFA Γ Q) (Adm Pi : Q → Q → Prop) (Rej : Set Q) (sep : Γ)
    (D0 : Lettered α C) (P0 : PosChan α C) (d : ℕ) :
    ((∃ w : List Γ, (w ≠ [] ∧ IsReaderHole M Adm Rej w ∧
        ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some sep ∧
          Pi (runPrefix M w x) (runPrefix M w y)) ∧ depth w ≤ d) →
      ∃ w : List Γ, (w ≠ [] ∧ IsReaderHole M Adm Rej w ∧
        ∃ x y, IsComp w x y ∧ w[x + w.length - y]? = some sep ∧
          Pi (runPrefix M w x) (runPrefix M w y)) ∧ depth w ≤ d ∧
        w.length ≤ anchoredLengthBound (Fintype.card Q) d) ∧
    ((∃ w, PosHole D0 P0 w ∧ depth w ≤ d) →
      ∃ w, PosHole D0 P0 w ∧ depth w ≤ d ∧
        w.length ≤ anchoredLengthBound (Fintype.card C) d) ∧
    ∀ N, anchoredDictionaryBound N d ≤ 2 ^ anchoredExponent N d ∧
      anchoredLengthBound N d ≤ 2 ^ 2 ^ (5 * anchoredExponent N d + 6) := by
  refine ⟨?_, ?_, fun N => ⟨anchoredDictionaryBound_le N d, anchoredLengthBound_le N d⟩⟩
  · rintro ⟨w, hw, hd⟩
    have hb := (lem_mo_base M Adm Pi Rej sep).2
    obtain ⟨v, hv, ⟨i, hi, hu⟩, hlen⟩ :=
      exists_short_posHole_elementary ((hb w).mp hw) ⟨depth w, hd, isUnary_depth w⟩
    exact ⟨v, (hb v).mpr hv, (depth_le_of_isUnary hu).trans hi, hlen⟩
  · rintro ⟨w, hw, hd⟩
    obtain ⟨v, hv, ⟨i, hi, hu⟩, hlen⟩ :=
      exists_short_posHole_elementary hw ⟨depth w, hd, isUnary_depth w⟩
    exact ⟨v, hv, (depth_le_of_isUnary hu).trans hi, hlen⟩

/-- **Theorem (Short mortal holes)**, `thm:mo-short`.
Form: L-sharp of I is anchoredLengthBound at the state count of the reader and the depth bound of lem:mo-depth, written out.
-/
theorem thm_mo_short {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') (h : I.HasMortalHole) :
    ∃ u t, I.IsMortalHole u t ∧ u.length + 1 + t.length ≤
      anchoredLengthBound
        (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
          Fintype.card SA * Fintype.card SB')
        (2 * (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
          Fintype.card SA * Fintype.card SB') * Fintype.card SA - 1) := by
  obtain ⟨u, t, hm⟩ := h
  obtain ⟨u', t', hm', hlen⟩ := Self.exists_short_mortalHole I hm
  simp only [Mortal.mortalHoleBound] at hlen
  exact ⟨u', t', hm', by omega⟩

/-- **Corollary (Mortal holes are decidable)**, `cor:mo-decidable`.
Form: Decidability is a computable definition, the executable procedure Self.decideHasMortalHole, together with the bounded search over words of length at most L-sharp of I that it performs.
-/
def cor_mo_decidable {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') :
    Decidable I.HasMortalHole ×'
    (I.HasMortalHole ↔
      ∃ u ∈ wordsUpTo (anchoredLengthBound
          (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB')
          (2 * (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB') * Fintype.card SA - 1)),
        ∃ t ∈ wordsUpTo (anchoredLengthBound
          (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB')
          (2 * (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB') * Fintype.card SA - 1)),
          I.IsMortalHole u t) :=
  ⟨Self.decideHasMortalHole I, Self.hasMortalHole_iff_bounded I⟩

/-- **Theorem (Short holes)**, `thm:mo-decide`.
Form: Lnm is pumpHoleBound and L-sharp of I is written out as in thm:mo-short. Decidability is a computable definition for instances with (FH): the executable bounded search SelfTwoWordInstance.decideBoundedHole at the bound selfHoleBound, transported along hasHole_iff_bounded.
-/
def thm_mo_decide {α : Type*} [Fintype α] [DecidableEq α]
    {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
    (I : Self.SelfTwoWordInstance α SA SB SA' SB') (hfh : I.ForcedHeads) :
    Decidable I.HasHole ×'
    (I.HasHole ↔ ∃ u t, I.IsHole u t ∧ u.length + t.length ≤
      max (pumpHoleBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA')
          (Fintype.card SB'))
        (anchoredLengthBound
          (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB')
          (2 * (1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
            Fintype.card SA * Fintype.card SB') * Fintype.card SA - 1))) :=
  ⟨@decidable_of_iff _ _ (I.hasHole_iff_bounded _ (Self.shortHoleBoundSelf α) hfh).symm
      (I.decideBoundedHole _),
    fun hh => I.shortHoleBoundSelf_transport _ (Self.shortHoleBoundSelf α) hfh hh,
      fun ⟨u, t, hh, _⟩ => ⟨u, t, hh⟩⟩

/-- **Lemma (Transport of continuation letters)**, `lem:mo-transport`.
Form: The expansion is expand l v' with block cuts cutP l v' i; only the data of the alignment lemma are assumed, from which (x, y) is a comparison; letters are optional list entries. Marker avoidance is not required.
-/
theorem lem_mo_transport {Γ : Type*} (ℓ : Γ) (v' : List (List Γ)) {i i' x y : ℕ}
    (hii' : i < i') (hi' : i' < v'.length) (xh xh' yh : List Γ)
    (hx : v'[i] = xh ++ yh) (hy : v'[i'] = xh' ++ yh) (hc : IsComp v' (i + 1) (i' + 1))
    (hxe : x = cutP ℓ v' i + xh.length) (hye : y = cutP ℓ v' i' + xh'.length) :
    ∃ hr : (i + 1) + v'.length - (i' + 1) < v'.length,
      i < (i + 1) + v'.length - (i' + 1) ∧
      x + (expand ℓ v').length - y = cutP ℓ v' ((i + 1) + v'.length - (i' + 1)) ∧
      (expand ℓ v')[cutP ℓ v' ((i + 1) + v'.length - (i' + 1))]? =
        (v'[(i + 1) + v'.length - (i' + 1)] ++ [ℓ])[0]? := by
  have hr : (i + 1) + v'.length - (i' + 1) < v'.length := by omega
  refine ⟨hr, by omega, ?_, ?_⟩
  · subst hxe hye
    exact continuation_cutP ℓ v' i i' (by omega) hi' xh xh' yh hx hy hc.2.2
  · have h := getElem?_expand ℓ v' _ hr 0 (Nat.zero_le _)
    rwa [Nat.add_zero] at h

/-- **Lemma (Anchored exchange types)**, `lem:mo-types`.
Form: The number of types is the cardinality of the type space, the codomain of anchoredType at the protected letters; the bound holds at every level below the depth of every nonempty word. Level zero is included; Inhabited supplies the default letter of the canonical hierarchy, which is unused because the word and its hierarchy levels are nonempty.
-/
theorem lem_mo_types {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]
    (D0 : Lettered α Q) {w : List α} {i d : ℕ} (hw : w ≠ []) (hid : i < depth w)
    (hd : depth w ≤ d) :
    Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) (Pset D0 w i) ×
      PosRows (Qset Q i) (Uset D0 w i) (Pset D0 w i)) ≤
      Fintype.card Q ^ Fintype.card Q * 2 ^ (5 * Fintype.card Q ^ 2 +
        10 * Fintype.card Q * (Fintype.card Q + d) * (d + 1) + 7 * Fintype.card Q + 1) := by
  rw [← anchoredTypeBound_eq]
  exact card_anchoredType_le D0 hw hid hd

/-- **Lemma (Anchored isolated exchange)**, `lem:mo-exchange`.
Form: The letter map h is identify a b; dictionaries are compared through alphCard and start counts through sCount. The canonical hierarchy uses an Inhabited alphabet; a letter is available from the nonempty hole, and the default is never used.
-/
theorem lem_mo_exchange {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    [DecidableEq Q] {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α} {i : ℕ}
    {a b : Alph α i} (hw : PosHole D0 P0 w) (hi : 1 ≤ i) (hid : i < depth w)
    (ha : Isolated (hierOf w i) (Pset D0 w i) a) (hb : Isolated (hierOf w i) (Pset D0 w i) b)
    (hab : a ≠ b)
    (ht : anchoredType D0 P0 w i (Pset D0 w i) a = anchoredType D0 P0 w i (Pset D0 w i) b)
    (hlen : (expandTo (markOf w) i [b]).length ≤ (expandTo (markOf w) i [a]).length) :
    PosHole D0 P0 (expandTo (markOf w) i ((hierOf w i).map (identify a b))) ∧
    depth (expandTo (markOf w) i ((hierOf w i).map (identify a b))) = depth w ∧
    (expandTo (markOf w) i ((hierOf w i).map (identify a b))).length ≤ w.length ∧
    (∀ j, sCount D0 (expandTo (markOf w) i ((hierOf w i).map (identify a b))) j =
      sCount D0 w j) ∧
    (∀ j, alphCard (expandTo (markOf w) i ((hierOf w i).map (identify a b))) j ≤
      alphCard w j) ∧
    (hierOf (expandTo (markOf w) i ((hierOf w i).map (identify a b))) i).toFinset =
      (hierOf w i).toFinset.erase a := by
  obtain ⟨hr, hp, hl, hc, -⟩ := posIsolated_merge_spec hw hi hid ha hb hab ht hlen
  refine ⟨hp, hr.depth_eq, hl, hr.sCount_eq, hc, ?_⟩
  have hlev : hierOf (expandTo (markOf w) i ((hierOf w i).map (identify a b))) i =
      (hierOf w i).map (identify a b) := hr.level 0
  rw [hlev]
  refine Finset.Subset.antisymm (Lettered.toFinset_identify_subset hab hb.1) fun c hc' => ?_
  obtain ⟨hca, hcm⟩ := Finset.mem_erase.mp hc'
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨c, List.mem_toFinset.mp hcm, identify_of_ne hca⟩)

/-- **Lemma (Normal form and bounded dictionaries)**, `lem:mo-dictionary`(1).
Form: Anchored normality is PosNormal; dictionaries are compared through alphCard and start counts through sCount. The canonical hierarchy uses an Inhabited alphabet; a letter is available from the nonempty hole, and the default is never used.
-/
theorem lem_mo_dictionary_1 {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    [DecidableEq Q] {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α}
    (hw : PosHole D0 P0 w) :
    ∃ w', PosHole D0 P0 w' ∧ PosNormal D0 P0 w' ∧ depth w' = depth w ∧
      w'.length ≤ w.length ∧ (∀ i, sCount D0 w' i = sCount D0 w i) ∧
      ∀ i, alphCard w' i ≤ alphCard w i := by
  obtain ⟨w', h1, h2, h3, h4, h5, h6⟩ := exists_posNormal_form hw
  exact ⟨w', h1, h6, h2, h3, h4, h5⟩

/-- **Lemma (Normal form and bounded dictionaries)**, `lem:mo-dictionary`(2).
Form: g_i is alphCard w i and b_i is the cardinality of boundaryPairs; A-sharp and G-sharp are anchoredAllowance and anchoredDictionaryBound. The unnumbered consequence is included. Inhabited supplies the default letter of the canonical hierarchy, which is unused on nonempty holes.
-/
theorem lem_mo_dictionary_2 {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    [DecidableEq Q] (D0 : Lettered α Q) (P0 : PosChan α Q) (d : ℕ) :
    (∀ w, PosHole D0 P0 w → PosNormal D0 P0 w → depth w ≤ d →
      alphCard w (depth w) = 1 ∧
      ∀ i, 1 ≤ i → i < depth w →
        alphCard w i ≤ anchoredAllowance (Fintype.card Q) d +
          2 * (boundaryPairs (hierOf w i)).card ∧
        2 * (boundaryPairs (hierOf w i)).card ≤
          (anchoredAllowance (Fintype.card Q) d - 1) * (3 ^ (depth w - 1 - i) - 1) ∧
        alphCard w i ≤ 1 + (anchoredAllowance (Fintype.card Q) d - 1) * 3 ^ (depth w - 1 - i) ∧
        1 + (anchoredAllowance (Fintype.card Q) d - 1) * 3 ^ (depth w - 1 - i) ≤
          anchoredDictionaryBound (Fintype.card Q) d) ∧
    ∀ w, PosHole D0 P0 w → depth w ≤ d →
      ∃ v, PosHole D0 P0 v ∧ depth v = depth w ∧ v.length ≤ w.length ∧
        ∀ i, 1 ≤ i → i ≤ depth v → alphCard v i ≤ anchoredDictionaryBound (Fintype.card Q) d := by
  refine ⟨fun w hw hn hd => ⟨?_, fun i hi hid => ?_⟩,
    fun w hw hd => exists_bounded_dictionary_posHole hw hd⟩
  · refine le_antisymm (alphCard_depth_le_one w) (Finset.card_pos.mpr ?_)
    exact (List.toFinset_nonempty_iff _).mpr (hierOf_ne_nil hw.1.ne_nil _)
  · have hA : 1 ≤ anchoredAllowance (Fintype.card Q) d := by unfold anchoredAllowance; omega
    have hg : ∀ j, 1 ≤ j → j < depth w → alphCard w j ≤ anchoredAllowance (Fintype.card Q) d +
        2 * (boundaryPairs (hierOf w j)).card :=
      fun j hj hjd => posNormalAt_alphCard_le hw (hn j hj hjd) hjd hd
    refine ⟨hg i hi hid, boundary_count_le_of_allowance hw.1.ne_nil hA hg hi hid,
      alphCard_le_of_allowance hw.1.ne_nil hA hg hi hid, ?_⟩
    unfold anchoredDictionaryBound
    have hp : 3 ^ (depth w - 1 - i) ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := Nat.mul_le_mul (Nat.sub_le (anchoredAllowance (Fintype.card Q) d) 1) hp
    omega

/-- **Lemma (Positive unary words)**, `lem:mo-unary`.
Form: The unary word z^m is List.replicate m z.
-/
theorem lem_mo_unary {Γ C : Type*} [Fintype C] (D : Lettered Γ C) (P : PosChan Γ C) (z : Γ)
    {m : ℕ} (hm : PosHole D P (List.replicate m z)) :
    ∃ m', 1 ≤ m' ∧ m' ≤ 3 * Fintype.card C ∧ PosHole D P (List.replicate m' z) := by
  obtain ⟨n, h1, h2, h3⟩ := unary_posHole_shorten D P z hm
  exact ⟨n, h1, h2.trans (min_le_right _ _), h3⟩

/-- **Lemma (Agreement under derivation)**, `lem:mo-agreement`.
Form: Agreement with channels is PosAgree, between monitors with a shared core type and possibly different alphabets; the support and the family of blocks are lists.
-/
theorem lem_mo_agreement {Γ Γ' C : Type*} {U : Lettered Γ C} {V : Lettered Γ' C}
    {PU : PosChan Γ C} {PV : PosChan Γ' C} {ρ : Γ → Γ'} {E : List Γ}
    (h : PosAgree U V PU PV ρ E) {ℓ : Γ} (hℓ : ℓ ∈ E)
    (F : List (List Γ)) (hF : ∀ X ∈ F, ∀ a ∈ X, a ∈ E) (hFℓ : ∀ X ∈ F, ℓ ∉ X) :
    PosAgree (der U ℓ) (der V (ρ ℓ)) (posDer U PU ℓ) (posDer V PV (ρ ℓ)) (List.map ρ) F ∧
    ∀ X ∈ F, ρ ℓ ∉ X.map ρ := by
  refine ⟨h.derive hℓ F hF, fun X hX hmem => ?_⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
  exact hFℓ X hX (h.neg.inj a (hF X hX a ha) ℓ hℓ he ▸ ha)

/-- **Lemma (Positive summaries)**, `lem:mo-summary`(1).
Form: A column word is a list of columns, maps from Fin k to Option Gamma with none as padding, and its current tuple is dec; the fields form a PosColumnState and their meanings are psumm; the prefixes of a valid word are its takes. State finiteness and marker avoidance are not required for this invariant.
-/
theorem lem_mo_summary_1 {Γ C : Type*} (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ) (k : ℕ)
    (w : List (Fin k → Option Γ)) (hw : Valid w) (n : ℕ) :
    (pcolDFA D P ℓ k).eval (w.take n) = psumm D P ℓ k (dec (w.take n)) :=
  pcolDFA_eval D P ℓ k _ (hw.sublist (List.take_sublist n w))

/-- **Lemma (Positive summaries)**, `lem:mo-summary`(2).
Form: The final positive summary is psumm of the tuple, by item (1); determination is stated as equal summaries giving equal rows of the derived channel, followed by the explicit formulas; the first-letter field is an optional Prop. State finiteness and marker avoidance are not required for these formulas.
-/
theorem lem_mo_summary_2 {Γ C : Type*} (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ) (k : ℕ)
    (Ws : Fin k → List Γ) :
    let s := psumm D P ℓ k Ws
    let T : Fin k → Option C → C → Prop := fun a c d =>
      s.posSummary.terminalAdmission a c d ∨ s.events a c d ∨ (s.pending a c d ∧ P.Φ ℓ)
    (∀ Ws' : Fin k → List Γ, psumm D P ℓ k Ws' = s → ∀ a b : Fin k,
      (∀ c, (posDer D P ℓ).F c (Ws' a) ↔ (posDer D P ℓ).F c (Ws a)) ∧
      (∀ c c', (posDer D P ℓ).R (some (c, Ws' a)) (some (c', Ws' b)) ↔
        (posDer D P ℓ).R (some (c, Ws a)) (some (c', Ws b))) ∧
      (∀ c c', (posDer D P ℓ).S (some (c, Ws' a)) (some (c', Ws' b)) ↔
        (posDer D P ℓ).S (some (c, Ws a)) (some (c', Ws b))) ∧
      ((posDer D P ℓ).Φ (Ws' a) ↔ (posDer D P ℓ).Φ (Ws a))) ∧
    (∀ a, (posDer D P ℓ).Φ (Ws a) ↔
      (∃ p, s.first a = some p ∧ p) ∨ (s.first a = none ∧ P.Φ ℓ)) ∧
    (∀ a b c c',
      ((posDer D P ℓ).R (some (c, Ws a)) (some (c', Ws b)) ↔
        s.posSummary.ladderAdmission a b c c') ∧
      ((posDer D P ℓ).S' (some (c, Ws a)) (some (c', Ws b)) ↔
        s.posSummary.ladderAdmission a b c c')) ∧
    (∀ a b c c', (posDer D P ℓ).S (some (c, Ws a)) (some (c', Ws b)) ↔
      T a c (s.summary.exit b c')) ∧
    (∀ a c, (posDer D P ℓ).F c (Ws a) ↔
      P.F (s.summary.exit a c) ℓ ∨ T a c (s.summary.exit a c)) ∧
    ∀ L, ¬ (posDer D P ℓ).R none L ∧ ¬ (posDer D P ℓ).R L none ∧
      ¬ (posDer D P ℓ).S none L ∧ ¬ (posDer D P ℓ).S L none ∧
      ¬ (posDer D P ℓ).S' none L ∧ ¬ (posDer D P ℓ).S' L none := by
  intro s T
  refine ⟨fun Ws' hs a b => pos_type_of_psumm D P ℓ k hs a b, fun a => ?_,
    fun a b c c' => ⟨Iff.rfl, Iff.rfl⟩,
    fun a b c c' => term_decode D P ℓ c (Ws a) _,
    fun a c => or_congr Iff.rfl (term_decode D P ℓ c (Ws a) _), fun L => ?_⟩
  · change At P.Φ (Ws a ++ [ℓ]) 0 ↔ (∃ p, (Ws a).head?.map P.Φ = some p ∧ p) ∨
      ((Ws a).head?.map P.Φ = none ∧ P.Φ ℓ)
    rw [phi_decode P ℓ (Ws a)]
    cases (Ws a).head?.map P.Φ with
    | none => simp
    | some q =>
      simp only [Option.getD_some, Option.some.injEq, reduceCtorEq, false_and, or_false]
      exact ⟨fun h => ⟨q, rfl, h⟩, fun ⟨_, hp, h⟩ => hp ▸ h⟩
  · rcases L with _ | ⟨c, X⟩ <;> exact ⟨id, id, id, id, id, id⟩

/-- **Lemma (Positive column shortening)**, `lem:mo-columns`.
Form: The family is a list of at most k blocks; subsequences are sublists, and injectivity is stated on the list.
-/
theorem lem_mo_columns {Γ C : Type*} [Fintype C] [DecidableEq C] (D : Lettered Γ C)
    (P : PosChan Γ C) (ℓ : Γ) (k : ℕ) (F : List (List Γ)) (hk : F.length ≤ k)
    (hℓ : ∀ X ∈ F, ℓ ∉ X) :
    ∃ τ : List Γ → List Γ,
      (∀ X ∈ F, (τ X).Sublist X ∧ (τ X).length < pcolBound (Fintype.card C) k ∧ ℓ ∉ τ X) ∧
      (∀ X ∈ F, ∀ Y ∈ F, τ X = τ Y → X = Y) ∧
      PosAgree (der D ℓ) (der D ℓ) (posDer D P ℓ) (posDer D P ℓ) τ F := by
  obtain ⟨τ, hA, hτ⟩ := exists_short_pos_letters D P ℓ k F hk
  exact ⟨τ, fun X hX => ⟨(hτ X hX).1, (hτ X hX).2, fun h => hℓ X hX ((hτ X hX).1.subset h)⟩,
    hA.neg.inj, hA⟩

/-- **Lemma (Supported compression with channels)**, `lem:mo-compression`.
Form: Markers are sequences over all levels, of which only those below j are used; Exp is expandTo, validity of the image family is Admissible, and E_j is a duplicate-free list. Inhabited supplies the default letter of the canonical hierarchy, which is unused because w and its hierarchy levels are nonempty.
-/
theorem lem_mo_compression {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    (D0 : Lettered α Q) (P0 : PosChan α Q) {w : List α} (hw : w ≠ []) {d g j : ℕ}
    (hj : j ≤ d) (hg : ∀ h, 1 ≤ h → h ≤ j → alphCard w h ≤ g) (E : List (Alph α j))
    (hE : E.Nodup) (hsub : ∀ x ∈ E, x ∈ hierOf w j) :
    ∃ (ℓ' : (i : ℕ) → Alph α i) (ρ : Alph α j → Alph α j),
      (∀ x ∈ E, ∀ y ∈ E, ρ x = ρ y → x = y) ∧
      PosAgree (tower D0 (markOf w) j) (tower D0 ℓ' j) (posTower D0 P0 (markOf w) j)
        (posTower D0 P0 ℓ' j) ρ E ∧
      (∀ x ∈ E, (expandTo ℓ' j [ρ x]).length ≤ pcolBound (Fintype.card Q + d + 1) g ^ j) ∧
      Admissible ℓ' j (E.map ρ) := by
  obtain ⟨ℓ', ρ, hA, hadm, hlen⟩ := shorten_pos_level_supported D0 P0 hw hj hg E hE hsub
  exact ⟨ℓ', ρ, hA.neg.inj, hA, hlen, hadm⟩

/-- **Lemma (Closed form)**, `lem:mo-closed-form`.
Form: G-sharp, L-sharp and Xi-sharp are anchoredDictionaryBound, anchoredLengthBound and anchoredExponent; N at least 1 is not needed.
-/
theorem lem_mo_closed_form (N d : ℕ) :
    anchoredDictionaryBound N d ≤ 2 ^ anchoredExponent N d ∧
    anchoredLengthBound N d ≤ 2 ^ 2 ^ (5 * anchoredExponent N d + 6) :=
  ⟨anchoredDictionaryBound_le N d, anchoredLengthBound_le N d⟩

end DeciENSSE.Paper
