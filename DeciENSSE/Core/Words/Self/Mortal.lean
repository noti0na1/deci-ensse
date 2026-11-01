import DeciENSSE.Core.Words.Self.Basic
import DeciENSSE.Core.Words.Mortal.Bound

/-! # Mortal holes with target self events

The reader includes target-target admissions. Elementary anchored compression
preserves self-event exclusion and the head witness while shortening mortal holes.

## Main declarations

- `Self.mortal_depth`
- `Self.exists_short_mortalHole`
- `mortalShortHoleBoundSelf`
-/

namespace DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Words.Mortal

variable {α : Type*} [Fintype α] [DecidableEq α]
open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.RejectedTail DeciNSSE.LetteredHierarchy
open DeciENSSE.Anchored

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SelfTwoWordInstance α SA SB SA' SB')

/-- The added channel compares active target states only. Strictness comes
from `IsComp`, rather than from the state predicate. -/
def SelfAdm : RState SA SB SA' SB' → RState SA SB SA' SB' → Prop
  | .act b _, .act b' _ => (b, b') ∈ I.SelfGuard
  | _, _ => False

/-- Retain cross admissions and add target self admissions. -/
def Adm (p q : RState SA SB SA' SB') : Prop :=
  Mortal.Adm I.toTwoWordInstance p q ∨ SelfAdm I p q

/-- Target self admission is decidable on reader states. -/
instance instDecidableSelfAdm : DecidableRel (SelfAdm I) := by
  intro p q
  cases p <;> cases q <;> unfold SelfAdm <;> infer_instance

/-- The union of cross and self admission is decidable. -/
instance instDecidableAdm : DecidableRel (Adm I) := by
  intro p q
  unfold Adm
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
/-- The target self channel is exactly the absence of self events, including
an event whose second endpoint is the first rejected cut itself. -/
theorem no_self_admitted_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    (∀ s e, IsComp (sepWord u t) s e →
      ¬ SelfAdm I (runPrefix (reader I.toTwoWordInstance) (sepWord u t) s)
        (runPrefix (reader I.toTwoWordInstance) (sepWord u t) e)) ↔ I.NoSelf t := by
  rw [I.noSelf_iff]
  constructor
  · intro h i k hev
    obtain ⟨hik, ⟨hi, hk, hp⟩, ⟨l, hl, hkl⟩, hg⟩ := hev
    have he : j = l := by simpa [hj] using hl
    subst l
    apply h (u.length + 1 + i) (u.length + 1 + k)
      ((target_comparison_iff u t hi hk).mpr ⟨hik, hp⟩)
    rw [run_target I.toTwoWordInstance hsafe hm hj hi, ite_eq_left (by omega : i ≤ j),
      run_target I.toTwoWordInstance hsafe hm hj hk, ite_eq_left hkl]
    exact hg
  · intro h s e hc hadm
    have hel : e ≤ u.length + 1 + t.length := by
      simpa only [length_sepWord] using hc.2.1
    by_cases hs : s ≤ u.length
    · rw [run_spine I.toTwoWordInstance hsafe hs] at hadm
      exact hadm
    · have hsq : s = u.length + 1 + (s - (u.length + 1)) := by omega
      have heq : e = u.length + 1 + (e - (u.length + 1)) := by
        have := hc.1; omega
      have hs' : s - (u.length + 1) ≤ t.length := by have := hc.1; omega
      have he' : e - (u.length + 1) ≤ t.length := by omega
      have hp := (target_comparison_iff u t hs' he').mp (hsq ▸ heq ▸ hc)
      rw [hsq, heq, run_target I.toTwoWordInstance hsafe hm hj hs',
        run_target I.toTwoWordInstance hsafe hm hj he'] at hadm
      split at hadm
      next hsj =>
        split at hadm
        next hej =>
          exact h _ _ ⟨hp.1, ⟨hs', he', hp.2⟩,
            ⟨j, by simp [hj], hej⟩, hadm⟩
        next => exact hadm
      next => exact hadm

omit [DecidableEq α] in
/-- Split the negative comparison condition into cross and target self channels. -/
theorem no_admitted_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    (∀ s e, IsComp (sepWord u t) s e →
      ¬ Adm I (runPrefix (reader I.toTwoWordInstance) (sepWord u t) s)
        (runPrefix (reader I.toTwoWordInstance) (sepWord u t) e)) ↔
    (∀ s ∈ Finset.range (u.length + 1), ∀ e ∈ Finset.range (t.length + 1),
      ¬ I.Event u t s e) ∧ I.NoSelf t := by
  rw [← Mortal.no_admitted_iff I.toTwoWordInstance hsafe hm hj,
    ← no_self_admitted_iff I hsafe hm hj]
  constructor
  · intro h
    exact ⟨fun s e hc ha => h s e hc (Or.inl ha),
      fun s e hc ha => h s e hc (Or.inr ha)⟩
  · rintro ⟨hcross, hself⟩ s e hc (ha | ha)
    · exact hcross s e hc ha
    · exact hself s e hc ha

/-- The Π-witness is unchanged; only negative admission is extended. -/
def PiHole (w : List (Option α)) : Prop :=
  IsReaderHole (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance) w ∧ HasPi
    I.toTwoWordInstance w

/-- A separated reader hole with a head witness is exactly a mortal self-aware hole. -/
theorem piHole_sep_iff (u t : Word α) :
    PiHole I (sepWord u t) ↔ I.IsMortalHole u t := by
  rw [I.isMortalHole_iff]
  constructor
  · rintro ⟨hh, hpi⟩
    have hc := (isReaderHole_iff _ _ _ _).mp hh
    obtain ⟨hs, hm, j, hj, hlen⟩ := (rejected_sep_iff I.toTwoWordInstance u t).mp hc.1
    have hn := (no_admitted_iff I hs hm hj).mp
      (fun s e hcomp => hc.2 s e hcomp.1 hcomp.2.1 hcomp.2.2)
    exact ⟨⟨⟨hs, by simp [hj], hn.1,
      (hasPi_sep_iff I.toTwoWordInstance hs hm hj).mp hpi⟩,
      hm, j, by simp [hj], hlen⟩, hn.2⟩
  · rintro ⟨⟨⟨hs, _, hne, hhead⟩, hm, j, hj, hlen⟩, hn⟩
    have hj' : I.J t = some j := by simpa using hj
    refine ⟨(isReaderHole_iff _ _ _ _).mpr ⟨(rejected_sep_iff I.toTwoWordInstance u t).mpr
      ⟨hs, hm, j, hj', hlen⟩, ?_⟩, (hasPi_sep_iff I.toTwoWordInstance hs hm hj').mpr hhead⟩
    intro s e hse he hp
    exact (no_admitted_iff I hs hm hj').mpr ⟨hne, hn⟩ s e ⟨hse, he, hp⟩

/-- Reader holes with a head witness decode into mortal self-aware word pairs. -/
theorem piReader_iff (w : List (Option α)) :
    PiHole I w ↔ ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  constructor
  · intro h
    obtain ⟨p, hcount, _⟩ := h.2
    obtain ⟨u, t, rfl⟩ := exists_sepWord w hcount
    exact ⟨u, t, rfl, (piHole_sep_iff I u t).mp h⟩
  · rintro ⟨u, t, rfl, h⟩
    exact (piHole_sep_iff I u t).mpr h

/-- The exact lettered-reader interface for anchored compression. -/
theorem ofReader_pi_iff (w : List (Option α)) :
    ((ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance)).IsHole w ∧
      HasPi I.toTwoWordInstance w) ↔ ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  rw [← piReader_iff]
  by_cases hw : w = []
  · subst w
    have hn : ¬ HasPi I.toTwoWordInstance [] := by rintro ⟨p, h, _⟩; simp at h
    simp [PiHole, hn]
  · rw [isHole_ofReader_iff _ _ _ hw]
    rfl

/-- Self admissions do not change the reader or the coarse depth bound. -/
theorem mortal_depth {u t : Word α} (h : I.IsMortalHole u t) :
    DeciNSSE.HierarchyDepth.depth (sepWord u t) ≤
      2 * Fintype.card (RState SA SB SA' SB') * Fintype.card SA - 1 :=
  Mortal.mortal_depth I.toTwoWordInstance ((I.isMortalHole_iff u t).mp h).1

/-- Combined signed input for the elementary anchored compression theorem. -/
theorem mortal_compression_input {u t : Word α} (h : I.IsMortalHole u t) :
    (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance)).IsHole (sepWord u t) ∧
      HasPi I.toTwoWordInstance (sepWord u t) ∧
      DeciNSSE.HierarchyDepth.depth (sepWord u t) ≤
        2 * Fintype.card (RState SA SB SA' SB') * Fintype.card SA - 1 := by
  have hh := (ofReader_pi_iff I (sepWord u t)).mpr ⟨u, t, rfl, h⟩
  exact ⟨hh.1, hh.2, mortal_depth I h⟩

/-- The positive channel bridge is generic in its negative admission. -/
theorem hasPi_iff_pos_of_count (w : List (Option α)) (hc : w.count none = 1) :
    HasPi I.toTwoWordInstance w ↔ Pos (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej
      I.toTwoWordInstance))
      (baseChan (reader I.toTwoWordInstance) (Pi I.toTwoWordInstance) none) w := by
  obtain ⟨u, t, rfl⟩ := exists_sepWord w hc
  have hb := pos_base_iff_anchored (reader I.toTwoWordInstance) (Adm I) (Pi I.toTwoWordInstance)
    (Rej I.toTwoWordInstance) none (sepWord u t) u.length
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
theorem hole_count_separator {w : List (Option α)}
    (hw : (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance)).IsHole w) :
    w.count none = 1 := by
  have hh := (isHole_ofReader_iff _ _ _ hw.ne_nil).mp hw
  exact rejected_count_separator I.toTwoWordInstance w ((isReaderHole_iff _ _ _ _).mp hh).1

/-- On reader holes, the head witness is exactly positivity of the base channel. -/
theorem hasPi_iff_pos_of_hole {w : List (Option α)}
    (hw : (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance)).IsHole w) :
    HasPi I.toTwoWordInstance w ↔ Pos (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej
      I.toTwoWordInstance))
      (baseChan (reader I.toTwoWordInstance) (Pi I.toTwoWordInstance) none) w :=
  hasPi_iff_pos_of_count I w (hole_count_separator I hw)

/-- The empty word and words with multiple separators cannot be positive holes. -/
theorem not_posHole_of_separator_count {w : List (Option α)}
    (hc : w.count none ≠ 1) :
    ¬ PosHole (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance))
      (baseChan (reader I.toTwoWordInstance) (Pi I.toTwoWordInstance) none) w :=
  fun hw => hc (hole_count_separator I hw.1)

/-- Wordwise signed correspondence in the exact generic positive-channel API. -/
theorem posHole_pi_iff (w : List (Option α)) :
    PosHole (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance))
      (baseChan (reader I.toTwoWordInstance) (Pi I.toTwoWordInstance) none) w ↔
      ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  rw [← ofReader_pi_iff I w]
  exact and_congr_right (fun hw => (hasPi_iff_pos_of_hole I hw).symm)

/-- Generic anchored compression preserves the self-event exclusion and
head witness. The stronger length bound includes the separator; ForcedHeads is unused. -/
theorem exists_short_mortalHole {u t : Word α} (h : I.IsMortalHole u t) :
    ∃ u' t', I.IsMortalHole u' t' ∧
      u'.length + t'.length + 1 ≤
        mortalHoleBound (Fintype.card SA) (Fintype.card SB)
          (Fintype.card SA') (Fintype.card SB') := by
  obtain ⟨hh, hpi, hd⟩ := mortal_compression_input I h
  have hp : PosHole (ofReader (reader I.toTwoWordInstance) (Adm I) (Rej I.toTwoWordInstance))
      (baseChan (reader I.toTwoWordInstance) (Pi I.toTwoWordInstance) none) (sepWord u t) :=
    ⟨hh, (hasPi_iff_pos_of_hole I hh).mp hpi⟩
  obtain ⟨w', hw', -, hlen⟩ := exists_short_posHole_elementary hp
    ⟨DeciNSSE.HierarchyDepth.depth (sepWord u t), hd, DeciNSSE.HierarchyDepth.isUnary_depth _⟩
  obtain ⟨u', t', rfl, hm⟩ := (posHole_pi_iff I w').mp hw'
  refine ⟨u', t', hm, ?_⟩
  simpa only [mortalHoleBound, card_state, length_sepWord, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hlen

/-- The mortal-bound statement retains the forced target heads premise, though local
compression does not require it. -/
theorem mortalShortHoleBoundSelf : MortalShortHoleBoundSelf α mortalHoleBound := by
  intro a b c d I _ h
  obtain ⟨u, t, hm⟩ := h
  obtain ⟨u', t', hm', hlen⟩ := Self.exists_short_mortalHole I hm
  refine ⟨u', t', hm', ?_⟩
  simp only [Fintype.card_fin] at hlen
  omega

end DeciENSSE.Core.Words.Self
