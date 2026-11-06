import DeciNSSE.RejectedTail.Decision
import DeciNSSE.Holes.StartCores
import DeciNSSE.Holes.Columns

/-! # Interfaces to the hole library

Facts about the canonical hierarchy, hierarchy cores, exchange types and column
compression of the plain-entailment library (`DeciNSSE.Holes`), stated in the
form used by the paper's background section (`DeciENSSE.Paper.Background`).
-/

namespace DeciENSSE.Support.HoleCorrespondence
open DeciNSSE

section ColumnReplacement
open Holes CoAlignment LetteredHierarchy BoundedDepth Packets

/-- Shorten supported block letters while retaining all derived tables and the
terminal-admission summary, which agreement alone does not determine. -/
theorem short_letters_summary {Γ C : Type*} [Fintype C] [DecidableEq C]
    (D : Lettered Γ C) (ℓ : Γ) (k : ℕ) (E : List (List Γ))
    (hk : E.length ≤ k) :
    ∃ ψ : List Γ → List Γ, Agree (der D ℓ) (der D ℓ) ψ E ∧
      ∀ X ∈ E, (ψ X).Sublist X ∧ (ψ X).length < colBound (Fintype.card C) k ∧
        ∀ c d, (∃ p ≤ (ψ X).length, D.Λf (zlab D ℓ c (ψ X) p) (some (d, ℓ))) ↔
          ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (d, ℓ)) := by
  classical
  set Ws : Fin k → List Γ := fun a => E.getD a.1 [] with hWs
  obtain ⟨Ws', hsub, hlen, hsumm⟩ := exists_short_tuple D ℓ k Ws
  have hT := der_type_of_summ D ℓ k hsumm
  have hidx : ∀ X ∈ E, E.idxOf X < k := fun X hX =>
    (List.idxOf_lt_length_of_mem hX).trans_le hk
  let idx : ∀ X ∈ E, Fin k := fun X hX => ⟨E.idxOf X, hidx X hX⟩
  have hWsidx : ∀ X (hX : X ∈ E), Ws (idx X hX) = X := fun X hX => by
    simp only [hWs, idx]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hX), List.getElem_idxOf]
  let ψ : List Γ → List Γ := fun X => if hX : X ∈ E then Ws' (idx X hX) else X
  have hψ : ∀ X (hX : X ∈ E), ψ X = Ws' (idx X hX) := fun X hX => dite_eq_left hX
  refine ⟨ψ, ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, fun X hX => ?_⟩
  · intro X hX Y hY hXY
    rw [hψ X hX, hψ Y hY, (hT (idx X hX) (idx Y hY)).1, hWsidx X hX, hWsidx Y hY] at hXY
    exact hXY
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.1, hWsidx X hX]
  · intro X hX c
    rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.2.1, hWsidx X hX]
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛ]
    · simp [derΛ]
    · simp [derΛ]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.1, hWsidx X hL, hWsidx Y hL']
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · simp [derΛf]
    · simp [derΛf]
    · simp [derΛf]
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.2, hWsidx X hL, hWsidx Y hL']
  · rw [hψ X hX]
    refine ⟨?_, hlen _, ?_⟩
    · have := hsub (idx X hX)
      rwa [hWsidx X hX] at this
    · intro c d
      have ht := congrFun (congrFun (congrFun (congrArg CS.terminalAdmission hsumm)
        (idx X hX)) c) d
      change (∃ p ≤ (Ws' (idx X hX)).length,
        D.Λf (zlab D ℓ c (Ws' (idx X hX)) p) (some (d, ℓ))) =
        (∃ p ≤ (Ws (idx X hX)).length,
          D.Λf (zlab D ℓ c (Ws (idx X hX)) p) (some (d, ℓ))) at ht
      rw [hWsidx X hX] at ht
      exact Iff.of_eq ht

end ColumnReplacement

section Cores
open Holes CoAlignment LetteredHierarchy HierarchyDepth BoundedDepth
open NormalForm Exchange CoreOccurrences Cores
open scoped List

/-- Ordinary core positions strictly increase along every canonical level. -/
theorem corePos_strict {α : Type*} [DecidableEq α] [Inhabited α]
    {w : List α} (hw : w ≠ []) :
    ∀ j x y, x < y → y < (hierOf w j).length →
      ∀ p q, corePos w j x = some p → corePos w j y = some q → p < q
  | 0, x, y, hxy, _, p, q, hp, hq => by
      have hp' : x = p := Option.some.inj hp
      have hq' : y = q := Option.some.inj hq
      omega
  | j + 1, 0, _, _, _, _, _, hp, _ => by simp [corePos] at hp
  | j + 1, x + 1, 0, hxy, _, _, _, _, _ => by omega
  | j + 1, x + 1, y + 1, hxy, hy, p, q, hp, hq => by
      apply corePos_strict hw j _ _ ?_ ?_ p q hp hq
      · have hm := cutP_succ_strictMono (markOf w j) (hierOf w (j + 1))
          (by omega : x < y) (by omega)
        have hx := cutP_succ_pos (markOf w j) (hierOf w (j + 1)) x (by omega)
        omega
      · have hc := cutP_le_length (markOf w j) (hierOf w (j + 1)) (y + 1)
        have hpos := cutP_succ_pos (markOf w j) (hierOf w (j + 1)) y (by omega)
        rw [expand_hierOf hw j] at hc
        omega

/-- The next ordinary-core set consists exactly of occurrences before the greatest core. -/
theorem ordinaryCores_succ {α : Type*} [DecidableEq α] [Inhabited α]
    {w : List α} (hw : w ≠ []) {j e : ℕ} (he : IsGreatest (ordinaryCores w j) e) :
    ordinaryCores w (j + 1) = {p | p < e ∧ w.drop e <+: w.drop p} := by
  have hel : e < w.length := by
    obtain ⟨x, hx, hp⟩ := he.1
    exact corePos_lt hw j x hx e hp
  ext p
  change (∃ x < (hierOf w (j + 1)).length, corePos w (j + 1) x = some p) ↔ _
  constructor
  · intro hp
    obtain ⟨r, hr, hlen, hpre⟩ := (corePos_succ_iff_occurrence hw j p).mp hp
    rw [rho_at_greatest hw he, Option.some.injEq] at hr
    subst r
    simp only [List.length_drop] at hlen
    exact ⟨by omega, hpre⟩
  · rintro ⟨hp, hpre⟩
    apply (corePos_succ_iff_occurrence hw j p).mpr
    exact ⟨w.drop e, rho_at_greatest hw he, by simp only [List.length_drop]; omega, hpre⟩

/-- The exchange-type space has the paper's uniform bound at every bounded level. -/
theorem exchange_types_le {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] (D : Lettered α Q) {w : List α} (hw : w ≠ [])
    {i d : ℕ} (hi : i ≤ d) :
    Fintype.card (ClosedType (Qset Q i) (Uset D w i) (Pset D w i)) ≤
      normalTypeBound (Fintype.card Q) d := by
  have hs := StartCores.sCount_le_level D hw i
  have hp := card_Pset_le D w i
  refine (card_exType_le D w i (Pset D w i)).trans ?_
  unfold normalTypeBound typeBound
  gcongr <;> omega

/-- Deleting a column factor between equal automaton states preserves validity and summary. -/
theorem delete_columns {Γ C : Type*} (D : Lettered Γ C) (ℓ : Γ) (k : ℕ)
    (a b z : List (Fin k → Option Γ)) (hv : Packets.Valid (a ++ b ++ z))
    (he : (colDFA D ℓ k).eval a = (colDFA D ℓ k).eval (a ++ b)) :
    Packets.Valid (a ++ z) ∧
      summ D ℓ k (Packets.dec (a ++ z)) = summ D ℓ k (Packets.dec (a ++ b ++ z)) := by
  have hv' := hv.sublist ((List.sublist_append_left a b).append (List.Sublist.refl z))
  refine ⟨hv', ?_⟩
  rw [← colEval D ℓ k _ hv', ← colEval D ℓ k _ hv]
  change (colDFA D ℓ k).evalFrom (colDFA D ℓ k).start (a ++ z) =
    (colDFA D ℓ k).evalFrom (colDFA D ℓ k).start ((a ++ b) ++ z)
  rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
  exact congrArg (fun q => (colDFA D ℓ k).evalFrom q z) he

/-- Agreement transports marker avoidance on its support. -/
theorem avoids_map {Γ Γ' C : Type*} {D : Lettered Γ C} {D' : Lettered Γ' C}
    {ρ : Γ → Γ'} {E : List Γ} (h : Agree D D' ρ E) {ℓ : Γ} (hℓ : ℓ ∈ E)
    {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (ha : ℓ ∉ X) : ρ ℓ ∉ X.map ρ := by
  rintro hm
  obtain ⟨a, ha', he⟩ := List.mem_map.mp hm
  exact ha ((h.inj a (hX a ha') ℓ hℓ he) ▸ ha')

/-- Letterwise maps preserve unary levels. -/
theorem unary_map {Γ Γ' : Type*} (ρ : Γ → Γ') {w : List Γ} (hu : IsUnary w) :
    IsUnary (w.map ρ) := by
  rintro a ha b hb
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
  exact congrArg ρ (hu a' ha' b' hb')

/-- The isolated exchange map satisfies the hypotheses of the level-map lemma
`DeciNSSE.LevelMaps.levelMap_spec`: it identifies no unequal predecessor pair, makes the
mapped level a hole of the level monitor, maps the level dictionary into itself, fixes the
start prefix letterwise and preserves the run of cores. -/
theorem isolated_levelMap_hyps {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] {D : Lettered α Q} {w : List α} {i : ℕ} {x y : Alph α i}
    (hw : D.IsHole w) (hx : Isolated (hierOf w i) (Pset D w i) x)
    (hy : Isolated (hierOf w i) (Pset D w i) y)
    (ht : exType D w i (Pset D w i) x = exType D w i (Pset D w i) y) :
    LevelMaps.NoCollapse (identify x y) (hierOf w i) ∧
    (tower D (markOf w) i).IsHole ((hierOf w i).map (identify x y)) ∧
    (∀ a ∈ hierOf w i, identify x y a ∈ hierOf w i) ∧
    (∀ a ∈ (hierOf w i).take (sCount D w i), identify x y a = a) ∧
    ∀ k, (tower D (markOf w) i).core ((hierOf w i).map (identify x y)) k =
      (tower D (markOf w) i).core (hierOf w i) k := by
  obtain ⟨hhole, hcore⟩ := isolated_merge D hw hx hy.2.1 ht
  refine ⟨LevelMaps.noCollapse_of_isComp_iff
      (isComp_identify_iff fun h => hx.partners_protected hw.ne_nil D y hy.2.1 h.symm),
    hhole, fun a ha => ?_, fun a ha => identify_of_ne fun he => hx.2.1 ?_, hcore⟩
  · by_cases hax : a = x
    · rw [hax, identify_self_left]; exact hy.1
    · rw [identify_of_ne hax]; exact ha
  · rw [← he]
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha)

/-- **Supported compression with its recursion.** The compression of
`DeciNSSE.BoundedDepth.shorten_level_supported`, together with the data of its recursion:
supports `Es h` with `Es j = E`, column shortenings `τ h` and level maps `ρ h`. At every
level `h < j`, the support consists of the marker of level `h` and the letters of the
shortened blocks of the support above, and lies in the original dictionary; the shortening
agrees with the canonical tower on the support above, gives sub-words shorter than the
column bound, and the level map above is the shortening followed by the level map below,
whose image of the old marker is the new marker. -/
theorem shorten_level_traced {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    (D : Lettered α Q) {w : List α} (hw : w ≠ []) {d g j : ℕ} (hj : j ≤ d)
    (hg : PositiveDictionaryBound w j g) (E : List (Alph α j)) (hE : E.Nodup)
    (hsub : ∀ x ∈ E, x ∈ hierOf w j) :
    ∃ (ℓ' : (i : ℕ) → Alph α i) (ρ : (h : ℕ) → Alph α h → Alph α h)
      (Es : (h : ℕ) → List (Alph α h)) (τ : (h : ℕ) → Alph α (h + 1) → Alph α (h + 1)),
      Es j = E ∧
      Agree (tower D (markOf w) j) (tower D ℓ' j) (ρ j) E ∧ Admissible ℓ' j (E.map (ρ j)) ∧
      (∀ x ∈ E, (expandTo ℓ' j [ρ j x]).length ≤ descentFactor (Fintype.card Q) d g ^ j) ∧
      ∀ h < j, (Es h).Nodup ∧
        (∀ a, a ∈ Es h ↔ a = markOf w h ∨ ∃ X ∈ Es (h + 1), a ∈ τ h X) ∧
        (∀ a ∈ Es h, a ∈ hierOf w h) ∧
        Agree (tower D (markOf w) (h + 1)) (tower D (markOf w) (h + 1)) (τ h) (Es (h + 1)) ∧
        (∀ X ∈ Es (h + 1), (τ h X).Sublist X ∧
          (τ h X).length < colBound (Fintype.card Q + h) g ∧
          ρ (h + 1) X = (τ h X).map (ρ h)) ∧
        ℓ' h = ρ h (markOf w h) := by
  classical
  induction j with
  | zero =>
      exact ⟨markOf w, fun _ => id, Function.update (fun h => ([] : List (Alph α h))) 0 E,
        fun _ => id, Function.update_self _ _ _, Agree.refl _ _, trivial,
        fun x _ => by simp [expandTo], fun h hh => absurd hh (Nat.not_lt_zero h)⟩
  | succ j ih =>
      have hadm : Admissible (markOf w) (j + 1) E :=
        admissible_of_subset (markOf w) (j + 1) E _ (admissible_hierOf hw _)
          (hierOf_ne_nil hw _) hsub
      obtain ⟨ψ, hψA, hψ⟩ := exists_short_letters (tower D (markOf w) j) (markOf w j) g E
        (length_le_of_dictionaryBound hg hE hsub)
      rw [card_cores j] at hψ
      set Ebig : List (Alph α j) := (markOf w j :: (E.map ψ).flatten).dedup with hEbig
      have hmemBig : ∀ X ∈ E, ∀ a ∈ ψ X, a ∈ Ebig := fun X hX a ha =>
        List.mem_dedup.mpr (List.mem_cons_of_mem _
          (List.mem_flatten.mpr ⟨ψ X, List.mem_map_of_mem hX, ha⟩))
      have hℓBig : markOf w j ∈ Ebig := List.mem_dedup.mpr List.mem_cons_self
      have hsubBig : ∀ a ∈ Ebig, a ∈ hierOf w j := by
        intro a ha
        rcases List.mem_cons.mp (List.mem_dedup.mp ha) with rfl | ha
        · exact markOf_mem hw j
        · obtain ⟨Y, hY, haY⟩ := List.mem_flatten.mp ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact mem_lower_dictionary hw (hsub X hX) ((hψ X hX).1.subset haY)
      have hmemIff : ∀ a, a ∈ Ebig ↔ a = markOf w j ∨ ∃ X ∈ E, a ∈ ψ X := by
        intro a
        simp only [hEbig, List.mem_dedup, List.mem_cons, List.mem_flatten, List.mem_map]
        aesop
      obtain ⟨ℓ'', ρ, Es, τ, hEs, hA, hadm'', hsize, htr⟩ :=
        ih (by omega) (fun t ht htd => hg t ht (by omega)) Ebig (List.nodup_dedup _) hsubBig
      set ℓ' : (i : ℕ) → Alph α i := Function.update ℓ'' j (ρ j (markOf w j)) with hℓ'
      have hℓ'j : ℓ' j = ρ j (markOf w j) := Function.update_self _ _ _
      have hℓ'lt : ∀ t < j, ℓ' t = ℓ'' t := fun t ht => Function.update_of_ne (by omega) _ _
      have htw : tower D ℓ' j = tower D ℓ'' j := tower_congr D j hℓ'lt
      have htw1 : tower D ℓ' (j + 1) = der (tower D ℓ'' j) (ρ j (markOf w j)) := by
        show der (tower D ℓ' j) (ℓ' j) = _
        rw [htw, hℓ'j]
      have hlast : Ebig.Nodup ∧ (∀ a, a ∈ Ebig ↔ a = markOf w j ∨ ∃ X ∈ E, a ∈ ψ X) ∧
          (∀ a ∈ Ebig, a ∈ hierOf w j) ∧
          Agree (tower D (markOf w) (j + 1)) (tower D (markOf w) (j + 1)) ψ E ∧
          (∀ X ∈ E, (ψ X).Sublist X ∧ (ψ X).length < colBound (Fintype.card Q + j) g ∧
            (ψ X).map (ρ j) = (ψ X).map (ρ j)) ∧
          ℓ' j = ρ j (markOf w j) :=
        ⟨List.nodup_dedup _, hmemIff, hsubBig, hψA,
          fun X hX => ⟨(hψ X hX).1, (hψ X hX).2, rfl⟩, hℓ'j⟩
      refine ⟨ℓ', Function.update ρ (j + 1) (fun X => (ψ X).map (ρ j)),
        Function.update Es (j + 1) E, Function.update τ j ψ, Function.update_self _ _ _,
        ?_, ?_, ?_, ?_⟩
      · rw [Function.update_self, htw1]
        exact hψA.comp (hA.derive hℓBig (E.map ψ) (by
          intro Y hY a ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact hmemBig X hX a ha))
      · rw [Function.update_self]
        exact admissible_update_map ℓ'' (ρ j) hℓBig
          (fun a ha h => hA.inj a ha (markOf w j) hℓBig h)
          hadm'' ψ hmemBig (fun X hX h => hadm.1 X hX ((hψ X hX).1.subset h))
      · intro X hX
        rw [Function.update_self]
        refine (length_expandTo_update_le ℓ'' (ρ j) (markOf w j) (ψ X)
          (B := descentFactor (Fintype.card Q) d g ^ j) fun y hy => hsize y ?_).trans ?_
        · rcases List.mem_append.mp hy with h1 | h1
          · exact hmemBig X hX y h1
          · rw [List.mem_singleton.mp h1]
            exact hℓBig
        · rw [pow_succ']
          apply Nat.mul_le_mul_right
          exact (hψ X hX).2.trans_le (colBound_mono_core (by omega) (by omega))
      · intro h hh
        rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | hh
        · rw [Function.update_of_ne (show h ≠ j + 1 by omega),
            Function.update_of_ne (show h + 1 ≠ j + 1 by omega),
            Function.update_of_ne (show h ≠ j by omega),
            Function.update_of_ne (show h + 1 ≠ j + 1 by omega),
            Function.update_of_ne (show h ≠ j + 1 by omega), hℓ'lt h hh]
          exact htr h hh
        · subst hh
          rw [Function.update_of_ne (Nat.ne_add_one _), Function.update_self,
            Function.update_self, Function.update_self,
            Function.update_of_ne (Nat.ne_add_one _), hEs]
          exact hlast

end Cores

end DeciENSSE.Support.HoleCorrespondence
