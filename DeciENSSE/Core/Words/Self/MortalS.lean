import DeciENSSE.Core.Words.Self.SS2Self
import DeciENSSE.Core.Words.Mortal.Bound

/-! # Mortal holes with target self events

The reader includes target-target admissions. Elementary anchored compression
preserves self-event exclusion and the head witness while shortening mortal holes.

## Main declarations

- `Mortal.mortal_depthS`
- `Mortal.exists_short_mortalHoleS`
- `mortalShortHoleBoundS`
-/

set_option autoImplicit false

namespace DeciENSSE.Core

variable {α : Type*} [Fintype α] [DecidableEq α]
namespace Mortal
open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.RejectedTail DeciNSSE.LetteredHierarchy
open DeciENSSE.Anchored

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2Self α SA SB SA' SB')

/-- The added channel compares active target states only. Strictness comes
from `IsComp`, rather than from the state predicate. -/
def SelfAdm : RState SA SB SA' SB' → RState SA SB SA' SB' → Prop
  | .act b _, .act b' _ => (b, b') ∈ I.SelfGuard
  | _, _ => False

/-- Retain cross admissions and add target self admissions. -/
def AdmS (p q : RState SA SB SA' SB') : Prop :=
  Adm I.toSS2 p q ∨ SelfAdm I p q

/-- Target self admission is decidable on reader states. -/
instance instDecidableSelfAdm : DecidableRel (SelfAdm I) := by
  intro p q
  cases p <;> cases q <;> unfold SelfAdm <;> infer_instance

/-- The union of cross and self admission is decidable. -/
instance instDecidableAdmS : DecidableRel (AdmS I) := by
  intro p q
  unfold AdmS
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Target comparisons are precisely strict suffix-prefix comparisons. -/
theorem target_comparison_iff (u t : Word α) {i j : ℕ}
    (_hi : i ≤ t.length) (hj : j ≤ t.length) :
    IsComp (sepWord u t) (u.length + 1 + i) (u.length + 1 + j) ↔
      i < j ∧ (t.drop j).IsPrefix (t.drop i) := by
  simp only [IsComp, length_sepWord, drop_target,
    List.prefix_map_iff_of_injective (Option.some_injective _)]
  constructor
  · rintro ⟨hij, _, hp⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hij, hp⟩
    exact ⟨by omega, by omega, hp⟩

omit [DecidableEq α] in
/-- The new negative channel is exactly the absence of self events, including
an event whose second endpoint is the first rejected cut itself. -/
theorem no_self_admitted_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    (∀ s e, IsComp (sepWord u t) s e →
      ¬ SelfAdm I (runPrefix (reader I.toSS2) (sepWord u t) s)
        (runPrefix (reader I.toSS2) (sepWord u t) e)) ↔ I.NoSelf t := by
  rw [I.noSelf_iff]
  constructor
  · intro h i k hev
    obtain ⟨hik, ⟨hi, hk, hp⟩, ⟨l, hl, hkl⟩, hg⟩ := hev
    have he : j = l := by simpa [hj] using hl
    subst l
    apply h (u.length + 1 + i) (u.length + 1 + k)
      ((target_comparison_iff u t hi hk).mpr ⟨hik, hp⟩)
    rw [run_target I.toSS2 hsafe hm hj hi, ite_eq_left (by omega : i ≤ j),
      run_target I.toSS2 hsafe hm hj hk, ite_eq_left hkl]
    exact hg
  · intro h s e hc hadm
    have hel : e ≤ u.length + 1 + t.length := by
      simpa only [length_sepWord] using hc.2.1
    by_cases hs : s ≤ u.length
    · rw [run_spine I.toSS2 hsafe hs] at hadm
      exact hadm
    · have hsq : s = u.length + 1 + (s - (u.length + 1)) := by omega
      have heq : e = u.length + 1 + (e - (u.length + 1)) := by
        have := hc.1; omega
      have hs' : s - (u.length + 1) ≤ t.length := by have := hc.1; omega
      have he' : e - (u.length + 1) ≤ t.length := by omega
      have hp := (target_comparison_iff u t hs' he').mp (hsq ▸ heq ▸ hc)
      rw [hsq, heq, run_target I.toSS2 hsafe hm hj hs',
        run_target I.toSS2 hsafe hm hj he'] at hadm
      split at hadm
      next hsj =>
        split at hadm
        next hej =>
          exact h _ _ ⟨hp.1, ⟨hs', he', hp.2⟩,
            ⟨j, by simp [hj], hej⟩, hadm⟩
        next => exact hadm
      next => exact hadm

omit [DecidableEq α] in
/-- Split the negative comparison condition into its old and new channels. -/
theorem no_admittedS_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    (∀ s e, IsComp (sepWord u t) s e →
      ¬ AdmS I (runPrefix (reader I.toSS2) (sepWord u t) s)
        (runPrefix (reader I.toSS2) (sepWord u t) e)) ↔
    (∀ s ∈ Finset.range (u.length + 1), ∀ e ∈ Finset.range (t.length + 1),
      ¬ I.Event u t s e) ∧ I.NoSelf t := by
  rw [← no_admitted_iff I.toSS2 hsafe hm hj,
    ← no_self_admitted_iff I hsafe hm hj]
  constructor
  · intro h
    exact ⟨fun s e hc ha => h s e hc (Or.inl ha),
      fun s e hc ha => h s e hc (Or.inr ha)⟩
  · rintro ⟨hcross, hself⟩ s e hc (ha | ha)
    · exact hcross s e hc ha
    · exact hself s e hc ha

/-- The Π-witness is unchanged; only negative admission is extended. -/
def PiHoleS (w : List (Option α)) : Prop :=
  IsReaderHole (reader I.toSS2) (AdmS I) (Rej I.toSS2) w ∧ HasPi I.toSS2 w

/-- A separated reader hole with a head witness is exactly a mortal self-aware hole. -/
theorem piHoleS_sep_iff (u t : Word α) :
    PiHoleS I (sepWord u t) ↔ I.IsMortalHoleS u t := by
  rw [I.isMortalHoleS_iff]
  constructor
  · rintro ⟨hh, hpi⟩
    have hc := (isReaderHole_iff _ _ _ _).mp hh
    obtain ⟨hs, hm, j, hj, hlen⟩ := (rejected_sep_iff I.toSS2 u t).mp hc.1
    have hn := (no_admittedS_iff I hs hm hj).mp
      (fun s e hcomp => hc.2 s e hcomp.1 hcomp.2.1 hcomp.2.2)
    exact ⟨⟨⟨hs, by simp [hj], hn.1,
      (hasPi_sep_iff I.toSS2 hs hm hj).mp hpi⟩,
      hm, j, by simp [hj], hlen⟩, hn.2⟩
  · rintro ⟨⟨⟨hs, _, hne, hhead⟩, hm, j, hj, hlen⟩, hn⟩
    have hj' : I.J t = some j := by simpa using hj
    refine ⟨(isReaderHole_iff _ _ _ _).mpr ⟨(rejected_sep_iff I.toSS2 u t).mpr
      ⟨hs, hm, j, hj', hlen⟩, ?_⟩, (hasPi_sep_iff I.toSS2 hs hm hj').mpr hhead⟩
    intro s e hse he hp
    exact (no_admittedS_iff I hs hm hj').mpr ⟨hne, hn⟩ s e ⟨hse, he, hp⟩

/-- Reader holes with a head witness decode into mortal self-aware word pairs. -/
theorem piReaderS_iff (w : List (Option α)) :
    PiHoleS I w ↔ ∃ u t, w = sepWord u t ∧ I.IsMortalHoleS u t := by
  constructor
  · intro h
    obtain ⟨p, hcount, _⟩ := h.2
    obtain ⟨u, t, rfl⟩ := exists_sepWord w hcount
    exact ⟨u, t, rfl, (piHoleS_sep_iff I u t).mp h⟩
  · rintro ⟨u, t, rfl, h⟩
    exact (piHoleS_sep_iff I u t).mpr h

/-- The exact lettered-reader interface for anchored compression. -/
theorem ofReaderS_pi_iff (w : List (Option α)) :
    ((ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2)).IsHole w ∧
      HasPi I.toSS2 w) ↔ ∃ u t, w = sepWord u t ∧ I.IsMortalHoleS u t := by
  rw [← piReaderS_iff]
  by_cases hw : w = []
  · subst w
    have hn : ¬ HasPi I.toSS2 [] := by rintro ⟨p, h, _⟩; simp at h
    simp [PiHoleS, hn]
  · rw [isHole_ofReader_iff _ _ _ hw]
    rfl

/-- Self admissions do not change the reader or the coarse depth bound. -/
theorem mortal_depthS {u t : Word α} (h : I.IsMortalHoleS u t) :
    DeciNSSE.HierarchyDepth.depth (sepWord u t) ≤
      2 * Fintype.card (RState SA SB SA' SB') * Fintype.card SA - 1 := by
  obtain ⟨j, hj, ht⟩ := h.2.2
  have hj' : I.J t = some j := by simpa using hj
  have hfirst := first_rejected_cut I.toSS2 h.1.1.1 h.2.1 hj'
  have hr := (rejected_sep_iff I.toSS2 u t).mpr ⟨h.1.1.1, h.2.1, j, hj', ht⟩
  have hd := rejected_depth (reader I.toSS2) (Rej I.toSS2)
    (sepWord_ne_nil u t) hr hfirst
  have he : (sepWord u t).length - (u.length + 1 + j) = t.length - j := by
    simp only [length_sepWord]; omega
  rw [he] at hd
  exact hd.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (by omega :
    t.length - j + 1 ≤ Fintype.card SA)) 1)

/-- Combined signed input for the elementary anchored compression theorem. -/
theorem mortal_compression_inputS {u t : Word α} (h : I.IsMortalHoleS u t) :
    (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2)).IsHole (sepWord u t) ∧
      HasPi I.toSS2 (sepWord u t) ∧
      DeciNSSE.HierarchyDepth.depth (sepWord u t) ≤
        2 * Fintype.card (RState SA SB SA' SB') * Fintype.card SA - 1 := by
  have hh := (ofReaderS_pi_iff I (sepWord u t)).mpr ⟨u, t, rfl, h⟩
  exact ⟨hh.1, hh.2, mortal_depthS I h⟩

/-- The positive channel bridge is generic in its negative admission. -/
theorem hasPiS_iff_pos_of_count (w : List (Option α)) (hc : w.count none = 1) :
    HasPi I.toSS2 w ↔ Pos (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2))
      (baseChan (reader I.toSS2) (Pi I.toSS2) none) w := by
  obtain ⟨u, t, rfl⟩ := exists_sepWord w hc
  have hb := pos_base_iff_anchored (reader I.toSS2) (AdmS I) (Pi I.toSS2)
    (Rej I.toSS2) none (sepWord u t) u.length
    (by simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using hc)
    ((separator_unique u t _).mpr rfl)
  constructor
  · rintro ⟨p, _, hp, s, e, ha, hpi⟩
    have he := (separator_unique u t p).mp hp
    subst p
    apply hb.mpr
    exact ⟨s, ha.1, ha.2.1 ▸ ha.2.2, ha.2.1 ▸ hpi⟩
  · intro hp
    obtain ⟨s, hs, he, hpi⟩ := hb.mp hp
    exact ⟨u.length, hc, (separator_unique u t _).mpr rfl,
      s, _, ⟨hs, rfl, he⟩, hpi⟩

/-- Rejection still forces exactly one separator under the stronger admission. -/
theorem holeS_count_separator {w : List (Option α)}
    (hw : (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2)).IsHole w) :
    w.count none = 1 := by
  have hh := (isHole_ofReader_iff _ _ _ hw.ne_nil).mp hw
  exact rejected_count_separator I.toSS2 w ((isReaderHole_iff _ _ _ _).mp hh).1

/-- On reader holes, the head witness is exactly positivity of the base channel. -/
theorem hasPiS_iff_pos_of_hole {w : List (Option α)}
    (hw : (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2)).IsHole w) :
    HasPi I.toSS2 w ↔ Pos (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2))
      (baseChan (reader I.toSS2) (Pi I.toSS2) none) w :=
  hasPiS_iff_pos_of_count I w (holeS_count_separator I hw)

/-- The empty word and words with multiple separators cannot be positive holes. -/
theorem not_posHoleS_of_separator_count {w : List (Option α)}
    (hc : w.count none ≠ 1) :
    ¬ PosHole (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2))
      (baseChan (reader I.toSS2) (Pi I.toSS2) none) w :=
  fun hw => hc (holeS_count_separator I hw.1)

/-- Wordwise signed correspondence in the exact generic positive-channel API. -/
theorem posHoleS_pi_iff (w : List (Option α)) :
    PosHole (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2))
      (baseChan (reader I.toSS2) (Pi I.toSS2) none) w ↔
      ∃ u t, w = sepWord u t ∧ I.IsMortalHoleS u t := by
  rw [← ofReaderS_pi_iff I w]
  exact and_congr_right (fun hw => (hasPiS_iff_pos_of_hole I hw).symm)

/-- Generic anchored compression preserves the self-event exclusion and
head witness. The stronger length bound includes the separator; FH is unused. -/
theorem exists_short_mortalHoleS {u t : Word α} (h : I.IsMortalHoleS u t) :
    ∃ u' t', I.IsMortalHoleS u' t' ∧
      u'.length + t'.length + 1 ≤
        mortalHoleBound (Fintype.card SA) (Fintype.card SB)
          (Fintype.card SA') (Fintype.card SB') := by
  obtain ⟨hh, hpi, hd⟩ := mortal_compression_inputS I h
  have hp : PosHole (ofReader (reader I.toSS2) (AdmS I) (Rej I.toSS2))
      (baseChan (reader I.toSS2) (Pi I.toSS2) none) (sepWord u t) :=
    ⟨hh, (hasPiS_iff_pos_of_hole I hh).mp hpi⟩
  obtain ⟨w', hw', -, hlen⟩ := exists_short_posHole_elementary hp
    ⟨DeciNSSE.HierarchyDepth.depth (sepWord u t), hd, DeciNSSE.HierarchyDepth.isUnary_depth _⟩
  obtain ⟨u', t', rfl, hm⟩ := (posHoleS_pi_iff I w').mp hw'
  refine ⟨u', t', hm, ?_⟩
  simpa only [mortalHoleBound, card_state, length_sepWord, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hlen

namespace Examples

/-- The mortal chain, with a nonempty self guard that does not fire
on the witness: its only strict target pair has B states `(0,1)`. -/
def smallS : SS2Self Bool (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toSS2 := DeciENSSE.Core.Mortal.Examples.small
  SelfGuard := {(1, 0)}

/-- The mortal witness has a nonempty self guard. -/
theorem smallS_selfGuard_nonempty : smallS.SelfGuard.Nonempty := by decide +kernel

/-- The mortal witness target has no self events. -/
theorem smallS_noSelf : smallS.NoSelf [true] := by decide +kernel

/-- The concrete binary word pair is a mortal self-aware hole. -/
theorem mortalS_01_1 : smallS.IsMortalHoleS [false, true] [true] :=
  (smallS.isMortalHoleS_iff _ _).mpr
    ⟨DeciENSSE.Core.Mortal.Examples.mortal_01_1, smallS_noSelf⟩

/-- The concrete instance satisfies the finite-head condition. -/
theorem smallS_fh : smallS.FH := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (DeciENSSE.Core.CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- This instance satisfies every premise of the public bound. -/
theorem smallS_hypotheses : smallS.FH ∧ smallS.HasMortalHoleS :=
  ⟨smallS_fh, _, _, mortalS_01_1⟩

/-- The separated binary witness is a reader hole with a head witness. -/
theorem piHoleS_01_sharp_1 : PiHoleS smallS (sepWord [false, true] [true]) :=
  (piHoleS_sep_iff smallS _ _).mpr mortalS_01_1

/-- The concrete mortal witness satisfies the reader, head, and depth conditions. -/
theorem compression_inputS :
    (ofReader (reader smallS.toSS2) (AdmS smallS) (Rej smallS.toSS2)).IsHole
      (sepWord [false, true] [true]) ∧
    HasPi smallS.toSS2 (sepWord [false, true] [true]) ∧
    DeciNSSE.HierarchyDepth.depth (sepWord [false, true] [true]) ≤ 167 := by
  simpa only [card_state, Fintype.card_fin] using
    mortal_compression_inputS smallS mortalS_01_1

/-- Apply the complete theorem, without evaluating its astronomical bound. -/
theorem mortalS_compressed :
    ∃ u t, smallS.IsMortalHoleS u t ∧
      u.length + t.length + 1 ≤ mortalHoleBound 4 2 2 2 := by
  simpa only [Fintype.card_fin] using exists_short_mortalHoleS smallS mortalS_01_1

/-- Empty words and words with two separators cannot be positive reader holes. -/
theorem malformed_wordsS :
    ¬ PosHole (ofReader (reader smallS.toSS2) (AdmS smallS) (Rej smallS.toSS2))
      (baseChan (reader smallS.toSS2) (Pi smallS.toSS2) none) [] ∧
    ¬ PosHole (ofReader (reader smallS.toSS2) (AdmS smallS) (Rej smallS.toSS2))
      (baseChan (reader smallS.toSS2) (Pi smallS.toSS2) none) [none, none] := by
  constructor <;> apply not_posHoleS_of_separator_count <;> decide

/-- Changing only the self guard blocks the same old mortal hole at `j = J`. -/
def blockedS : SS2Self Bool (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toSS2 := DeciENSSE.Core.Mortal.Examples.small
  SelfGuard := {(0, 1)}

/-- A changed self guard blocks the hole at the first rejected cut. -/
theorem blockedS_at_first_rejection :
    blockedS.J [true] = some 1 ∧ blockedS.SelfEvent [true] 0 1 ∧
      ¬ blockedS.IsMortalHoleS [false, true] [true] := by decide +kernel

/-- The blocked binary witness cannot give a reader hole with a head witness. -/
theorem blockedS_no_piHole : ¬ PiHoleS blockedS (sepWord [false, true] [true]) := by
  rw [piHoleS_sep_iff]
  exact blockedS_at_first_rejection.2.2

/-- A ternary mortal witness with a nonempty self guard. -/
def ternarySmallS : SS2Self (Fin 3) (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toSS2 := ternarySmall
  SelfGuard := {(1, 0)}

/-- The ternary word pair is a mortal self-aware hole. -/
theorem ternary_mortalS : ternarySmallS.IsMortalHoleS [0, 2] [2] :=
  (ternarySmallS.isMortalHoleS_iff _ _).mpr
    ⟨ternary_mortal_02_2, by decide +kernel⟩

/-- All public mortal-bound premises hold, with an active third letter. -/
theorem ternary_hypothesesS : ternarySmallS.SelfGuard.Nonempty ∧
    ternarySmallS.FH ∧ ternarySmallS.HasMortalHoleS := by
  refine ⟨by decide +kernel, ?_, _, _, ternary_mortalS⟩
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- Elementary compression shortens the concrete mortal self-aware hole. -/
theorem ternary_compressedS :
    ∃ u t, ternarySmallS.IsMortalHoleS u t ∧
      u.length + t.length + 1 ≤ mortalHoleBound 4 2 2 2 := by
  simpa only [Fintype.card_fin] using exists_short_mortalHoleS ternarySmallS ternary_mortalS

/-- The self channel includes the first rejected cut over a ternary alphabet. -/
def ternaryBlockedS : SS2Self (Fin 3) (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toSS2 := ternarySmall
  SelfGuard := {(0, 1)}

/-- The changed self guard also blocks the ternary witness at first rejection. -/
theorem ternary_blockedS : ternaryBlockedS.J [2] = some 1 ∧
    ternaryBlockedS.SelfEvent [2] 0 1 ∧
    ¬ PiHoleS ternaryBlockedS (sepWord [0, 2] [2]) := by
  rw [piHoleS_sep_iff]
  decide +kernel

end Examples
end Mortal

/-- The public mortal bound retains the finite-head premise, though local
compression does not require it. -/
theorem mortalShortHoleBoundS : MortalShortHoleBoundS α mortalHoleBound := by
  intro a b c d I _ h
  obtain ⟨u, t, hm⟩ := h
  obtain ⟨u', t', hm', hlen⟩ := Mortal.exists_short_mortalHoleS I hm
  refine ⟨u', t', hm', ?_⟩
  simp only [Fintype.card_fin] at hlen
  omega

/-- The separator supplies an inhabitant even for an empty source alphabet. -/
theorem mortalShortHoleBoundS_empty : MortalShortHoleBoundS (Fin 0) mortalHoleBound :=
  mortalShortHoleBoundS

/-- Exercise the exact public interface on the ternary self-guard witness. -/
theorem Mortal.Examples.ternary_public_boundS :
    ∃ u t, ternarySmallS.IsMortalHoleS u t ∧
      u.length + t.length ≤ mortalHoleBound 4 2 2 2 :=
  mortalShortHoleBoundS 4 2 2 2 ternarySmallS
    ternary_hypothesesS.2.1 ternary_hypothesesS.2.2

end DeciENSSE.Core
