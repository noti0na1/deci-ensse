import DeciENSSE.Anchored.Desubstitution
import DeciNSSE.Holes.NormalForm

/-! # Anchored exchange types and anchored normal forms

Merging two isolated letters of the same exchange type keeps a hole, its depth and its
start counts. To keep a positive hole, the type also records the positive rows of the
letter: its `F` row, its tables for `R`, `S` and `S'` against itself, protected letters and
the start label, and its `Φ` bit. Merging isolated letters with equal anchored types keeps
the core run, the comparisons and the positions of continuation letters, so it keeps the
positive condition. Repeated merges give an anchored-normal positive hole, whose dictionary
at each positive level below the unary top is bounded by the protected letters, one letter
per anchored type, and the endpoints of its boundary pairs. The exchange types and the
normal form without a channel are those of `DeciNSSE.Exchange` and `DeciNSSE.NormalForm`.

## Main declarations

- `PosSameType`, `pos_identify`: agreeing positive rows, and identification of letters with
  agreeing rows.
- `PosRows`, `posRowsOf`, `card_posRows`: the positive rows of a letter, and their number.
- `anchoredType`, `posIsolated_merge_spec`: anchored exchange types, and the anchored merge.
- `PosNormal`, `exists_posNormal_form`: anchored-normal positive holes.
- `alphCard_le_of_isolated_injOn`: dictionaries from any type map injective on isolated
  letters.
- `anchoredTypeBound`, `anchoredAllowance`, `posNormalAt_alphCard_le`: the dictionary
  allowance at an anchored-normal level.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth

section Identify
variable {Γ C : Type*} [DecidableEq Γ] (D : Lettered Γ C) (P : PosChan Γ C)

/-- Two letters have agreeing positive rows on the recorded ordinary cores `Qo`, used cores
`U` and protected letters `Z`. -/
structure PosSameType (Qo U : Set C) (Z : Set Γ) (x y : Γ) : Prop where
  /-- The same final tests from the recorded cores. -/
  f : ∀ q ∈ Qo, P.F q x ↔ P.F q y
  /-- Agreeing rows of `R`. -/
  rowsR : Lettered.PairRows P.R Qo U Z x y
  /-- Agreeing rows of `S`. -/
  rowsS : Lettered.PairRows P.S Qo U Z x y
  /-- Agreeing rows of `S'`. -/
  rowsS' : Lettered.PairRows P.S' Qo U Z x y
  /-- The same letter test. -/
  φ : P.Φ x ↔ P.Φ y

/-- Identifying letters with the same letter test preserves letter tests. -/
theorem at_identify_iff {Φ : Γ → Prop} {x y : Γ} (hφ : Φ x ↔ Φ y)
    (v : List Γ) (i : ℕ) : At Φ (v.map (identify x y)) i ↔ At Φ v i := by
  simp only [At, List.getElem?_map]
  cases h : v[i]? with
  | none => simp
  | some a =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    by_cases ha : a = x
    · subst ha; rw [identify_self_left]; exact hφ.symm
    · rw [identify_of_ne ha]

/-- Identifying a letter with one of the same transitions and positive rows, when all its
unequal comparison partners are protected, preserves the positive condition: the core run,
the comparisons and the positions of continuation letters do not change. -/
theorem pos_identify {Qo U : Set C} {Z : Set Γ} {v : List Γ} {x y : Γ}
    (hκ : ∀ q ∈ Qo, D.κ x q = D.κ y q) (hT : PosSameType P Qo U Z x y) (hy : y ∉ Z)
    (hpart : ∀ b, b ∉ Z → ¬ CoAligned v x b)
    (hQo : ∀ j (hj : j < v.length), v[j] = x → D.core v j ∈ Qo)
    (hU : ∀ j (hj : j < v.length), v[j] ∈ Z → D.core v j ∈ U)
    (hv : Pos D P v) : Pos D P (v.map (identify x y)) := by
  have hcore := D.core_identify hκ hQo
  have hcomp : ∀ s e, IsComp (v.map (identify x y)) s e ↔ IsComp v s e :=
    isComp_identify_iff (fun h => hpart y hy h.symm)
  have hat := at_identify_iff hT.φ v
  unfold Pos at hv ⊢
  rw [List.length_map]
  rcases hv with ⟨c, a, hl, hF⟩ | ⟨s, e, hc, he, hR, hφ⟩ | ⟨s, hs, hS⟩ | ⟨s, hs, hS, hφ⟩
  · left
    have hn : v ≠ [] := by rintro rfl; simp [Lettered.label] at hl
    obtain ⟨j, hlen⟩ : ∃ j, v.length = j + 1 :=
      ⟨v.length - 1, by have := List.length_pos_iff.mpr hn; omega⟩
    have hj : j < v.length := by omega
    rw [hlen, D.label_identify hcore hj]
    rw [hlen, D.label_succ v hj, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨_, _, rfl, ?_⟩
    by_cases hx : v[j] = x
    · rw [hx] at hF
      rw [hx, identify_self_left]
      exact (hT.f _ (hQo j hj hx)).mp hF
    · rw [identify_of_ne hx]
      exact hF
  · refine Or.inr (Or.inl ⟨s, e, (hcomp s e).mpr hc, he, ?_, (hat _).mpr hφ⟩)
    rw [D.pair_iff hT.rowsR hpart hQo hU hcore hc]
    exact hR
  · refine Or.inr (Or.inr (Or.inl ⟨s, hs, ?_⟩))
    exact (D.pair_iff hT.rowsS hpart hQo hU hcore (isComp_end v hs)).mpr hS
  · refine Or.inr (Or.inr (Or.inr ⟨s, hs, ?_, (hat _).mpr hφ⟩))
    exact (D.pair_iff hT.rowsS' hpart hQo hU hcore (isComp_end v hs)).mpr hS

end Identify

section Rows
variable {Γ C : Type*} (P : PosChan Γ C)

/-- The positive rows of a letter: the `F` row, the tables of `R`, `S`, `S'`, and `Φ`. -/
abbrev PosRows (Qo U : Finset C) (Z : Finset Γ) : Type _ :=
  (Qo → Prop) × Lettered.RowType Qo U Z × Lettered.RowType Qo U Z ×
    Lettered.RowType Qo U Z × Prop

/-- The positive rows of a letter. -/
def posRowsOf (Qo U : Finset C) (Z : Finset Γ) (x : Γ) : PosRows Qo U Z :=
  (fun q => P.F q.1 x, Lettered.rowsOf P.R Qo U Z x, Lettered.rowsOf P.S Qo U Z x,
    Lettered.rowsOf P.S' Qo U Z x, P.Φ x)

/-- Letters with equal positive rows have agreeing positive rows. -/
theorem posSameType_of_posRowsOf_eq {Qo U : Finset C} {Z : Finset Γ} {x y : Γ}
    (h : posRowsOf P Qo U Z x = posRowsOf P Qo U Z y) :
    PosSameType P (Qo : Set C) (U : Set C) (Z : Set Γ) x y := by
  simp only [posRowsOf, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun q hq => Iff.of_eq (congrFun h1 ⟨q, hq⟩), Lettered.pairRows_of_rowsOf_eq h2,
    Lettered.pairRows_of_rowsOf_eq h3, Lettered.pairRows_of_rowsOf_eq h4, Iff.of_eq h5⟩

/-- There are finitely many positive rows. -/
instance instFintypePosRows [DecidableEq C] [DecidableEq Γ] (Qo U : Finset C)
    (Z : Finset Γ) : Fintype (PosRows Qo U Z) :=
  @instFintypeProd _ _ inferInstance (@instFintypeProd _ _
    (DeciNSSE.Exchange.instFintypeRowType' Qo U Z) (@instFintypeProd _ _
      (DeciNSSE.Exchange.instFintypeRowType' Qo U Z) (@instFintypeProd _ _
        (DeciNSSE.Exchange.instFintypeRowType' Qo U Z) inferInstance)))

/-- The number of positive rows. -/
theorem card_posRows [DecidableEq C] [DecidableEq Γ] (Qo U : Finset C) (Z : Finset Γ) :
    Fintype.card (PosRows Qo U Z) =
      2 ^ (3 * Qo.card ^ 2 + 6 * Qo.card * U.card * Z.card + 4 * Qo.card + 1) := by
  simp only [PosRows, Lettered.RowType, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_prop, Fintype.card_coe]
  ring

end Rows

section Merge
open DeciNSSE.Exchange DeciNSSE.NormalForm DeciNSSE.LevelMaps DeciNSSE.HierarchyDepth
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]

/-- The anchored exchange type of a level letter: its exchange type and its positive rows in
the derived channel of the level. -/
def anchoredType (D0 : Lettered α Q) (P0 : PosChan α Q) (w : List α) (i : ℕ)
    (Z : Finset (Alph α i)) (x : Alph α i) :
    ClosedType (Qset Q i) (Uset D0 w i) Z × PosRows (Qset Q i) (Uset D0 w i) Z :=
  (exType D0 w i Z x, posRowsOf (posTower D0 P0 (markOf w) i) (Qset Q i) (Uset D0 w i) Z x)

/-- Merging two isolated letters of the same anchored type keeps a positive hole, its
canonical shape and its start counts, does not increase length or any dictionary, and
shrinks the dictionary of the level. -/
theorem posIsolated_merge_spec {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α} {i : ℕ}
    {x y : Alph α i} (hw : PosHole D0 P0 w) (hi : 1 ≤ i) (hid : i < depth w)
    (hx : Isolated (hierOf w i) (Pset D0 w i) x)
    (hy : Isolated (hierOf w i) (Pset D0 w i) y) (hxy : x ≠ y)
    (ht : anchoredType D0 P0 w i (Pset D0 w i) x = anchoredType D0 P0 w i (Pset D0 w i) y)
    (hlen : letterWeight w i y ≤ letterWeight w i x) :
    let w' := expandTo (markOf w) i ((hierOf w i).map (identify x y))
    LevelMapResult D0 w i (identify x y) w' ∧ PosHole D0 P0 w' ∧ w'.length ≤ w.length ∧
      (∀ j, alphCard w' j ≤ alphCard w j) ∧ alphCard w' i < alphCard w i := by
  dsimp only
  have ht1 : exType D0 w i (Pset D0 w i) x = exType D0 w i (Pset D0 w i) y :=
    congrArg Prod.fst ht
  have ht2 := posSameType_of_posRowsOf_eq _ (congrArg Prod.snd ht)
  obtain ⟨hr, hl, hc, hlt⟩ := isolated_merge_spec hw.1 hi hid hx hy hxy ht1 hlen
  refine ⟨hr, ⟨hr.hole, ?_⟩, hl, hc, hlt⟩
  have hw0 : w ≠ [] := hw.1.ne_nil
  have hT := sameType_of_exType_eq D0 ht1
  have hQ : ∀ j (hj : j < (hierOf w i).length), (hierOf w i)[j] = x →
      (tower D0 (markOf w) i).core (hierOf w i) j ∈ (Qset Q i : Set (Cores Q i)) := by
    intro j hj he
    exact core_mem_Qset_of_not_mem_Pset D0 hw0 i j hj (he ▸ hx.2.1)
  have hpos := ((pos_hierOf_iff D0 P0 hw0 i).mpr hw).2
  have hpos' := pos_identify (tower D0 (markOf w) i) (posTower D0 P0 (markOf w) i) hT.κ_eq ht2
    hy.2.1 (hx.partners_protected hw0 D0) hQ (fun j hj _ => core_mem_Uset D0 hw0 i j hj) hpos
  have hsub : ∀ a ∈ (hierOf w i).map (identify x y), a ∈ hierOf w i := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases hbx : b = x
    · rw [hbx, identify_self_left]; exact hy.1
    · rw [identify_of_ne hbx]; exact hb
  have hadm : Admissible (markOf w) i ((hierOf w i).map (identify x y)) :=
    admissible_of_subset _ i _ (hierOf w i) (admissible_hierOf hw0 i) (hierOf_ne_nil hw0 i) hsub
  have hne : (hierOf w i).map (identify x y) ≠ [] := by simpa using hierOf_ne_nil hw0 i
  exact (pos_expandTo_iff D0 P0 (markOf w) i _ hadm hne).mp hpos'

/-- Distinct isolated letters have distinct anchored types at this level. -/
def PosNormalAt (D0 : Lettered α Q) (P0 : PosChan α Q) (w : List α) (i : ℕ) : Prop :=
  ∀ x y, Isolated (hierOf w i) (Pset D0 w i) x → Isolated (hierOf w i) (Pset D0 w i) y →
    anchoredType D0 P0 w i (Pset D0 w i) x = anchoredType D0 P0 w i (Pset D0 w i) y → x = y

/-- Every positive non-unary level is anchored-normal. -/
def PosNormal (D0 : Lettered α Q) (P0 : PosChan α Q) (w : List α) : Prop :=
  ∀ i, 1 ≤ i → i < depth w → PosNormalAt D0 P0 w i

/-- Every positive hole has an anchored-normal positive hole of the same depth and start
counts, with no greater length or dictionary. -/
theorem exists_posNormal_form {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α}
    (hw : PosHole D0 P0 w) :
    ∃ w', PosHole D0 P0 w' ∧ depth w' = depth w ∧ w'.length ≤ w.length ∧
      (∀ i, sCount D0 w' i = sCount D0 w i) ∧
      (∀ i, alphCard w' i ≤ alphCard w i) ∧ PosNormal D0 P0 w' := by
  classical
  suffices H : ∀ n (v : List α), dictionaryPotential v = n → PosHole D0 P0 v →
      ∃ v', PosHole D0 P0 v' ∧ depth v' = depth v ∧ v'.length ≤ v.length ∧
        (∀ i, sCount D0 v' i = sCount D0 v i) ∧
        (∀ i, alphCard v' i ≤ alphCard v i) ∧ PosNormal D0 P0 v' from H _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hvn hv
    by_cases hn : PosNormal D0 P0 v
    · exact ⟨v, hv, rfl, le_rfl, fun _ => rfl, fun _ => le_rfl, hn⟩
    · simp only [PosNormal, PosNormalAt, not_forall] at hn
      obtain ⟨i, hn⟩ := hn
      push Not at hn
      obtain ⟨hi, hid, x, y, hx, hy, ht, hxy⟩ := hn
      have step : ∀ x y : Alph α i,
          Isolated (hierOf v i) (Pset D0 v i) x →
          Isolated (hierOf v i) (Pset D0 v i) y → x ≠ y →
          anchoredType D0 P0 v i (Pset D0 v i) x = anchoredType D0 P0 v i (Pset D0 v i) y →
          letterWeight v i y ≤ letterWeight v i x →
          ∃ v', PosHole D0 P0 v' ∧ depth v' = depth v ∧ v'.length ≤ v.length ∧
            (∀ j, sCount D0 v' j = sCount D0 v j) ∧
            (∀ j, alphCard v' j ≤ alphCard v j) ∧ PosNormal D0 P0 v' := by
        intro x y hx hy hxy ht hlen
        obtain ⟨hr, hp, hl, hc, hlt⟩ := posIsolated_merge_spec hv hi hid hx hy hxy ht hlen
        have hpot := dictionaryPotential_lt hr.depth_eq hc hid.le hlt
        rw [hvn] at hpot
        obtain ⟨v', hv', hd', hl', hs', hc', hn'⟩ := ih _ hpot _ rfl hp
        exact ⟨v', hv', hd'.trans hr.depth_eq, hl'.trans hl,
          fun j => (hs' j).trans (hr.sCount_eq j), fun j => (hc' j).trans (hc j), hn'⟩
      rcases le_total (letterWeight v i y) (letterWeight v i x) with hlen | hlen
      · exact step x y hx hy hxy ht hlen
      · exact step y x hy hx hxy.symm ht.symm hlen

end Merge

section Count
open DeciNSSE.Exchange DeciNSSE.NormalForm DeciNSSE.HierarchyDepth DeciNSSE.BoundaryPairs
  DeciNSSE.StartCores
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]

omit [Fintype Q] [DecidableEq Q] in
/-- A level dictionary is bounded by its protected letters, the size of any type space
on which the isolated letters are separated, and twice its boundary pairs. This generalizes
`DeciNSSE.NormalForm.normalAt_alphCard_le_types` from exchange types to any type map, with
the same proof. -/
theorem alphCard_le_of_isolated_injOn {D0 : Lettered α Q} {w : List α} {i : ℕ} {T : Type*}
    [Fintype T] (τ : Alph α i → T)
    (hn : ∀ x y, Isolated (hierOf w i) (Pset D0 w i) x → Isolated (hierOf w i) (Pset D0 w i) y →
      τ x = τ y → x = y) :
    alphCard w i ≤ (Pset D0 w i).card + Fintype.card T +
      2 * (boundaryPairs (hierOf w i)).card := by
  classical
  let v := hierOf w i
  let P := Pset D0 w i
  let S := v.toFinset.filter (Isolated v P)
  let B := boundaryPairs v
  let E := B.image Prod.fst ∪ B.image Prod.snd
  have hS : S.card ≤ Fintype.card T := by
    have hinj : Set.InjOn τ (S : Set (Alph α i)) := by
      intro x hx y hy he
      exact hn x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
    calc
      S.card = (S.image τ).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card T := Finset.card_le_univ _
  have hE : E.card ≤ 2 * B.card := by
    have hu := Finset.card_union_le (B.image Prod.fst) (B.image Prod.snd)
    have h1 : (B.image Prod.fst).card ≤ B.card := Finset.card_image_le
    have h2 : (B.image Prod.snd).card ≤ B.card := Finset.card_image_le
    dsimp only [E]
    omega
  have hsub : v.toFinset ⊆ P ∪ S ∪ E := by
    intro x hx
    have hxv := List.mem_toFinset.mp hx
    by_cases hxp : x ∈ P
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxp)
    by_cases hxi : Isolated v P x
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxi⟩))
    have hh : ¬ ∀ y, y ∈ v → y ∉ P → ¬ CoAlignedNT v x y :=
      fun h => hxi ⟨hxv, hxp, h⟩
    push Not at hh
    obtain ⟨y, _, _, hco⟩ := hh
    apply Finset.mem_union_right
    rcases coAlignedNT_iff.mp hco with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x, y), h, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y, x), h, rfl⟩)
  have hcard := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (P ∪ S) E
  have hu2 := Finset.card_union_le P S
  change v.toFinset.card ≤ P.card + Fintype.card T + 2 * B.card
  omega

/-- The number of anchored exchange types at depth at most `d`, for `N` cores. -/
def anchoredTypeBound (N d : ℕ) : ℕ :=
  normalTypeBound N d * 2 ^ (3 * N ^ 2 + 6 * N * (N + d) * (d + 1) + 4 * N + 1)

/-- Protected letters and isolated anchored types contribute this many letters. -/
def anchoredAllowance (N d : ℕ) : ℕ := d + 1 + anchoredTypeBound N d

/-- At an anchored-normal level below the unary top, the dictionary exceeds the allowance
by at most twice the number of boundary pairs. -/
theorem posNormalAt_alphCard_le {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α} {i d : ℕ}
    (hw : PosHole D0 P0 w) (hn : PosNormalAt D0 P0 w i) (hid : i < depth w)
    (hd : depth w ≤ d) :
    alphCard w i ≤ anchoredAllowance (Fintype.card Q) d +
      2 * (boundaryPairs (hierOf w i)).card := by
  have hs : sCount D0 w i ≤ d := (sCount_le_level D0 hw.1.ne_nil i).trans (by omega)
  have hp : (Pset D0 w i).card ≤ d + 1 := (card_Pset_le D0 w i).trans (by omega)
  have hU := card_Uset_le D0 w i
  have h := alphCard_le_of_isolated_injOn (anchoredType D0 P0 w i (Pset D0 w i)) hn
  have hT : Fintype.card (ClosedType (Qset Q i) (Uset D0 w i) (Pset D0 w i) ×
      PosRows (Qset Q i) (Uset D0 w i) (Pset D0 w i)) ≤
      anchoredTypeBound (Fintype.card Q) d := by
    rw [Fintype.card_prod, card_posRows, card_Qset]
    unfold anchoredTypeBound
    apply Nat.mul_le_mul
    · refine (card_exType_le D0 w i (Pset D0 w i)).trans ?_
      unfold normalTypeBound typeBound
      gcongr
    · apply Nat.pow_le_pow_right (by decide)
      have h1 : (Uset D0 w i).card ≤ Fintype.card Q + d := by omega
      have h2 : 6 * Fintype.card Q * (Uset D0 w i).card * (Pset D0 w i).card ≤
          6 * Fintype.card Q * (Fintype.card Q + d) * (d + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) hp
      omega
  unfold anchoredAllowance
  omega

end Count

end DeciENSSE.Anchored
