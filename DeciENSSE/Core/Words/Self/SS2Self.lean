import Mathlib.Tactic.Tauto
import DeciENSSE.Core.Words.Transport
import DeciENSSE.Core.Words.NonMortal

/-! # Two-word instances with target self guards

Target self events extend the two-word hole condition. State transport preserves
the resulting hole and bound interfaces. Words are spine first, target second.

## Main declarations

- `SS2Self`
- `SS2Self.IsHoleS`
- `ShortHoleBoundS`
- `SS2Self.shortHoleBoundS_transport`
-/

set_option autoImplicit false

namespace DeciENSSE.Core

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A two-word instance extended by a finite table of target self guards. -/
structure SS2Self (α : Type*) (SA SB SC SD : Type*) [Fintype SA] [Fintype SB]
    [Fintype SC] [Fintype SD] [DecidableEq SA] [DecidableEq SB]
    [DecidableEq SC] [DecidableEq SD] extends SS2 α SA SB SC SD where
  /-- Guarded pairs of target states for strict target self comparisons. -/
  SelfGuard : Finset (SB × SB)

namespace SS2Self
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
variable (I : SS2Self α SA SB SC SD)

/-- A guarded strict target comparison ending no later than the first rejection. -/
def SelfEvent (t : Word α) (i j : ℕ) : Prop :=
  i < j ∧ SS2.Cross t t i j ∧ (∃ k ∈ I.J t, j ≤ k) ∧
    (I.B.atCut t i, I.B.atCut t j) ∈ I.SelfGuard

/-- Target self events are decidable at fixed cuts. -/
instance instDecidableSelfEvent (t : Word α) (i j : ℕ) : Decidable (I.SelfEvent t i j) := by
  unfold SelfEvent SS2.Cross
  infer_instance

/-- No target self event occurs at any pair of cuts. -/
def NoSelf (t : Word α) : Prop :=
  ∀ i ∈ Finset.range (t.length + 1), ∀ j ∈ Finset.range (t.length + 1),
    ¬ I.SelfEvent t i j

/-- Absence of target self events is decidable. -/
instance instDecidableNoSelf (t : Word α) : Decidable (I.NoSelf t) := by
  unfold NoSelf
  infer_instance

/-- A hole whose target has no self events. -/
def IsHoleS (u t : Word α) : Prop := I.toSS2.IsHole u t ∧ I.NoSelf t

/-- The self-aware hole predicate is decidable on a fixed word pair. -/
instance instDecidableIsHoleS (u t : Word α) : Decidable (I.IsHoleS u t) := by
  unfold IsHoleS
  infer_instance

/-- Existence of a hole with no target self events. -/
def HasHoleS : Prop := ∃ u t, I.IsHoleS u t

/-- A self-event-free hole with a mortal endpoint and a short rejected tail. -/
def IsMortalHoleS (u t : Word α) : Prop :=
  I.IsHoleS u t ∧ I.Mortal (I.A.run u) ∧
    ∃ j ∈ I.J t, t.length - j < Fintype.card SA

/-- The mortal self-aware hole predicate is decidable. -/
instance instDecidableIsMortalHoleS (u t : Word α) : Decidable (I.IsMortalHoleS u t) := by
  unfold IsMortalHoleS
  infer_instance

/-- Existence of a mortal hole with no target self events. -/
def HasMortalHoleS : Prop := ∃ u t, I.IsMortalHoleS u t

/-- A finite continuation breaks every current target self event. -/
def CompletesSelf (t θ : Word α) : Prop :=
  ∀ i j, I.SelfEvent t i j → ¬ SS2.Keeps t t i j θ

/-- No current target self event survives the infinite continuation. -/
def SelfSurvivorFree (t : Word α) (ξ : ℕ → α) : Prop :=
  ∀ i j, I.SelfEvent t i j → ¬ SS2.Survives t t i j ξ

/-- A branching pre-hole or a thin pre-hole with both survivor conditions. -/
def NonMortalCaseS : Prop := ∃ u t, I.IsPreHole u t ∧
  (I.Branching (I.A.run u) ∨ (I.Thin (I.A.run u) ∧
    ∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ))

/-- The periodic shortening premise retains both survivor conditions. -/
def PurelyPeriodicShortPreHoleS [Inhabited α] (K : ℕ) : Prop :=
  ∀ q ξ, I.Thin q → I.Lasso q ξ → (∃ p, 0 < p ∧ StreamPeriod ξ p) →
    (∃ u t, I.IsPreHole u t ∧ I.A.run u = q ∧
      I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ) →
    ∃ u t, I.IsPreHole u t ∧ I.A.run u = q ∧
      I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ ∧ u.length < K ∧ t.length < K

omit [Fintype α] [DecidableEq α] in
/-- Absence of self events can be quantified over all natural cuts. -/
theorem noSelf_iff (t : Word α) : I.NoSelf t ↔ ∀ i j, ¬ I.SelfEvent t i j := by
  constructor
  · intro h i j he
    exact h i (Finset.mem_range.mpr (by have := he.2.1.1; omega))
      j (Finset.mem_range.mpr (by have := he.2.1.2.1; omega)) he
  · intro h i _ j _; exact h i j

omit [Fintype α] [DecidableEq α] in
/-- Self events cannot be aligned, so pre-holes need no extra aligned-event test. -/
theorem selfEvent_not_aligned {t : Word α} {i j : ℕ} (h : I.SelfEvent t i j) :
    ¬ SS2.Aligned t t i j := by
  intro ha
  have he := congrArg List.length ha.2.2
  simp only [List.length_drop] at he
  have := h.1
  have := ha.2.1
  omega

omit [Fintype α] [DecidableEq α] in
/-- Self completion can be checked over the finite set of target cuts. -/
theorem completesSelf_iff (t θ : Word α) : I.CompletesSelf t θ ↔
    ∀ i ∈ Finset.range (t.length + 1), ∀ j ∈ Finset.range (t.length + 1),
      I.SelfEvent t i j → ¬ SS2.Keeps t t i j θ := by
  constructor
  · intro h i _ j _; exact h i j
  · intro h i j he
    exact h i (Finset.mem_range.mpr (by have := he.2.1.1; omega))
      j (Finset.mem_range.mpr (by have := he.2.1.2.1; omega)) he

/-- Whether a finite continuation breaks every self event is decidable. -/
instance instDecidableCompletesSelf (t θ : Word α) : Decidable (I.CompletesSelf t θ) := by
  letI (i j : ℕ) : Decidable (SS2.Keeps t t i j θ) :=
    inferInstanceAs (Decidable (θ.IsPrefix (SS2.overhang t t i j ++ θ)))
  exact decidable_of_iff _ (I.completesSelf_iff t θ).symm

omit [Fintype α] [DecidableEq α] in
/-- A mortal self-aware hole is an ordinary mortal hole without self events. -/
theorem isMortalHoleS_iff (u t : Word α) :
    I.IsMortalHoleS u t ↔ I.toSS2.IsMortalHole u t ∧ I.NoSelf t := by
  simp only [IsMortalHoleS, IsHoleS, SS2.IsMortalHole]
  tauto

end SS2Self

/-- A state-count bound for holes with target self guards. -/
def ShortHoleBoundS (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SS2Self α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.HasHoleS → ∃ u t, I.IsHoleS u t ∧ u.length + t.length ≤ B a b c d

/-- A state-count bound for holes arising from the non-mortal self-aware case. -/
def NonMortalShortHoleBoundS (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SS2Self α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.NonMortalCaseS → ∃ u t, I.IsHoleS u t ∧ u.length + t.length ≤ B a b c d

/-- A state-count bound for mortal holes with target self guards. -/
def MortalShortHoleBoundS (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SS2Self α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → I.HasMortalHoleS →
      ∃ u t, I.IsMortalHoleS u t ∧ u.length + t.length ≤ B a b c d

/-- The three-case decomposition for instances with target self guards. -/
def ThreeCasesS (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  ∀ a b c d, ∀ I : SS2Self α (Fin a) (Fin b) (Fin c) (Fin d),
    I.FH → (I.HasHoleS ↔ I.NonMortalCaseS ∨ I.HasMortalHoleS)

/-- The maximum of non-mortal and mortal bounds bounds every self-aware hole. -/
theorem shortHoleBoundS_of_split {B₁ B₂ : HoleBound} (hc : ThreeCasesS α)
    (hn : NonMortalShortHoleBoundS α B₁) (hm : MortalShortHoleBoundS α B₂) :
    ShortHoleBoundS α (fun a b c d => max (B₁ a b c d) (B₂ a b c d)) := by
  intro a b c d I hfh hh
  rcases (hc a b c d I hfh).mp hh with h | h
  · obtain ⟨u, t, hu, hb⟩ := hn a b c d I hfh h
    exact ⟨u, t, hu, hb.trans (le_max_left _ _)⟩
  · obtain ⟨u, t, hu, hb⟩ := hm a b c d I hfh h
    exact ⟨u, t, hu.1, hb.trans (le_max_right _ _)⟩

end DeciENSSE.Core

namespace DeciENSSE.Core.SS2

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- The covariant regression bridge has no target self guards. -/
def toSelf (I : SS2 α SA SB SC SD) : (DeciENSSE.Core.SS2Self α) SA SB SC SD where
  toSS2 := I
  SelfGuard := ∅

omit [Fintype α] [DecidableEq α] in
/-- An instance with an empty self guard has no target self events. -/
@[simp] theorem noSelf_toSelf (I : SS2 α SA SB SC SD) (t : Word α) : I.toSelf.NoSelf t := by
  simp [DeciENSSE.Core.SS2Self.NoSelf, DeciENSSE.Core.SS2Self.SelfEvent, toSelf]

omit [Fintype α] [DecidableEq α] in
/-- Adding an empty self guard preserves the hole condition. -/
@[simp] theorem isHoleS_toSelf_iff (I : SS2 α SA SB SC SD) (u t : Word α) :
    I.toSelf.IsHoleS u t ↔ I.IsHole u t := by
  simp only [DeciENSSE.Core.SS2Self.IsHoleS, noSelf_toSelf, and_true]
  rfl

omit [Fintype α] [DecidableEq α] in
/-- Adding an empty self guard preserves the mortal-hole condition. -/
@[simp] theorem isMortalHoleS_toSelf_iff (I : SS2 α SA SB SC SD) (u t : Word α) :
    I.toSelf.IsMortalHoleS u t ↔ I.IsMortalHole u t := by
  rw [DeciENSSE.Core.SS2Self.isMortalHoleS_iff]
  simp only [noSelf_toSelf, and_true]
  rfl

end DeciENSSE.Core.SS2

namespace DeciENSSE.Core.SS2Self

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD TA TB TC TD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
  [Fintype TA] [Fintype TB] [Fintype TC] [Fintype TD]
  [DecidableEq TA] [DecidableEq TB] [DecidableEq TC] [DecidableEq TD]
variable (I : SS2Self α SA SB SC SD) (a : SA ≃ TA) (b : SB ≃ TB)
  (c : SC ≃ TC) (d : SD ≃ TD)

/-- Reuse parent transport; both self-guard coordinates use the target equivalence. -/
def rename : SS2Self α TA TB TC TD where
  toSS2 := I.toSS2.rename a b c d
  SelfGuard := I.SelfGuard.map (Equiv.prodCongr b b).toEmbedding

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves target self events. -/
@[simp] theorem rename_selfEvent (t : Word α) (i j : ℕ) :
    (I.rename a b c d).SelfEvent t i j ↔ I.SelfEvent t i j := by
  unfold SelfEvent
  change (_ ∧ _ ∧ (∃ k ∈ (I.toSS2.rename a b c d).J t, j ≤ k) ∧ _) ↔ _
  simp only [SS2.rename_J]
  simp [rename, SS2.rename]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves absence of self events. -/
@[simp] theorem rename_noSelf (t : Word α) :
    (I.rename a b c d).NoSelf t ↔ I.NoSelf t := by
  simp only [NoSelf, rename_selfEvent]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves self-aware holes. -/
@[simp] theorem rename_isHoleS (u t : Word α) :
    (I.rename a b c d).IsHoleS u t ↔ I.IsHoleS u t := by
  exact and_congr (I.toSS2.rename_isHole a b c d u t) (I.rename_noSelf a b c d t)

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves self-aware hole existence. -/
@[simp] theorem rename_hasHoleS : (I.rename a b c d).HasHoleS ↔ I.HasHoleS := by
  simp only [HasHoleS, rename_isHoleS]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves bounded self-aware holes. -/
theorem rename_boundedHoleS (L : ℕ) :
    (∃ u t, (I.rename a b c d).IsHoleS u t ∧ u.length + t.length ≤ L) ↔
      ∃ u t, I.IsHoleS u t ∧ u.length + t.length ≤ L := by simp

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves the finite-head condition. -/
@[simp] theorem rename_fh : (I.rename a b c d).FH ↔ I.FH :=
  I.toSS2.rename_fh a b c d

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves pre-holes. -/
@[simp] theorem rename_isPreHole (u t : Word α) :
    (I.rename a b c d).IsPreHole u t ↔ I.IsPreHole u t := by
  change (I.toSS2.rename a b c d).IsPreHole u t ↔ I.toSS2.IsPreHole u t
  simp only [SS2.IsPreHole, SS2.HasHeadEvent, SS2.rename_J,
    SS2.rename_headEvent, SS2.rename_event]
  exact and_congr (I.toSS2.rename_safeFrom a b c d I.A.start u) Iff.rfl

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves mortal self-aware holes. -/
@[simp] theorem rename_isMortalHoleS (u t : Word α) :
    (I.rename a b c d).IsMortalHoleS u t ↔ I.IsMortalHoleS u t := by
  rw [isMortalHoleS_iff, isMortalHoleS_iff]
  exact and_congr (I.toSS2.rename_isMortalHole a b c d u t) (I.rename_noSelf a b c d t)

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves mortal self-aware hole existence. -/
@[simp] theorem rename_hasMortalHoleS :
    (I.rename a b c d).HasMortalHoleS ↔ I.HasMortalHoleS := by
  simp only [HasMortalHoleS, rename_isMortalHoleS]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves self-event completion. -/
@[simp] theorem rename_completesSelf (t θ : Word α) :
    (I.rename a b c d).CompletesSelf t θ ↔ I.CompletesSelf t θ := by
  simp only [CompletesSelf, rename_selfEvent]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves self-survivor freeness. -/
@[simp] theorem rename_selfSurvivorFree (t : Word α) (ξ : ℕ → α) :
    (I.rename a b c d).SelfSurvivorFree t ξ ↔ I.SelfSurvivorFree t ξ := by
  simp only [SelfSurvivorFree, rename_selfEvent]

/-- Fin-indexed bounds apply to arbitrary finite state carriers, with unchanged words. -/
theorem shortHoleBoundS_transport (B : HoleBound) (hB : ShortHoleBoundS α B)
    (hfh : I.FH) (hh : I.HasHoleS) :
    ∃ u t, I.IsHoleS u t ∧ u.length + t.length ≤
      B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD) := by
  let a := Fintype.equivFin SA
  let b := Fintype.equivFin SB
  let c := Fintype.equivFin SC
  let d := Fintype.equivFin SD
  exact (rename_boundedHoleS I a b c d _).mp
    (hB _ _ _ _ (I.rename a b c d) ((rename_fh I a b c d).mpr hfh)
      ((rename_hasHoleS I a b c d).mpr hh))

end DeciENSSE.Core.SS2Self

namespace DeciENSSE.Core.SS2SelfExamples
open SS2Self

/-- Two states in each of the four automata; only empty heads are admitted. -/
def pending : SS2Self Bool (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  A := ⟨0, fun _ _ => 0⟩
  B := CoreExamples.emptyHeadDFA
  A' := CoreExamples.emptyHeadDFA
  B' := CoreExamples.emptyHeadDFA
  Bad := ∅
  Rej := {1}
  Guard := ∅
  Head := {(0, 0)}
  SelfGuard := {(0, 1)}

/-- The concrete instance satisfies the finite-head condition. -/
theorem pending_fh : pending.FH := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem pending_preHole : pending.IsPreHole [false] [false] := by decide +kernel
/-- The one-letter target has a self event at its two cuts. -/
theorem pending_event : pending.SelfEvent [false] 0 1 := by decide +kernel
/-- The pending example is a hole when self guards are ignored. -/
theorem pending_underlying_hole : pending.toSS2.IsHole [false] [false] := by decide +kernel
/-- The pending self event blocks the self-aware hole. -/
theorem pending_blocked : ¬ pending.IsHoleS [false] [false] := by decide +kernel

/-- Appending the other letter breaks the pending self event. -/
theorem pending_breaks : pending.CompletesSelf [false] [true] := by decide +kernel
/-- The extended word pair is a self-aware hole. -/
theorem pending_completed : pending.IsHoleS [false, true] [false, true] := by decide +kernel

/-- The initial state has two distinct safe continuations. -/
theorem pending_branching : pending.Branching 0 := by
  refine ⟨by decide, 0, ⟨[], by decide, rfl⟩,
    ⟨[false], by decide, by decide, rfl⟩, false, true, by decide, by decide, by decide⟩

/-- Both the hole and branching-case premises of the global interfaces are inhabited. -/
theorem pending_hypotheses : pending.FH ∧ pending.HasHoleS ∧ pending.NonMortalCaseS :=
  ⟨pending_fh, ⟨_, _, pending_completed⟩,
    ⟨_, _, pending_preHole, Or.inl pending_branching⟩⟩

/-- The target head accepts exactly [false]; its third state is the dead state. -/
def singletonHead : LDFA Bool (Fin 3) :=
  ⟨0, fun q c => if q = 0 ∧ c = false then 1 else 2⟩

/-- The head reader remains in its sink state. -/
theorem singletonHead_sink (w : Word Bool) : singletonHead.runFrom 2 w = 2 := by
  induction w with
  | nil => rfl
  | cons c w ih => simpa [LDFA.runFrom, singletonHead] using ih

/-- The head reader accepts exactly the one-letter word `[false]`. -/
theorem singletonHead_accept (w : Word Bool) : singletonHead.run w = 1 ↔ w = [false] := by
  cases w with
  | nil => decide +kernel
  | cons c w =>
    cases w with
    | nil => cases c <;> decide +kernel
    | cons d w =>
      have he : singletonHead.run (c :: d :: w) = singletonHead.runFrom 2 w := by
        cases c <;> cases d <;> rfl
      rw [he, singletonHead_sink]
      simp

/-- A unique underlying hole, with two-state A/B and a three-state target head. -/
def uniqueBlocked : SS2Self Bool (Fin 2) (Fin 2) (Fin 2) (Fin 3) where
  A := CoreExamples.emptyHeadDFA
  B := CoreExamples.emptyHeadDFA
  A' := ⟨0, fun _ _ => 0⟩
  B' := singletonHead
  Bad := {1}
  Rej := {1}
  Guard := ∅
  Head := {(0, 1)}
  SelfGuard := {(0, 1)}

/-- The concrete instance satisfies the finite-head condition. -/
theorem uniqueBlocked_fh : uniqueBlocked.FH := by
  intro p q hp _ γ hγ i hi
  have hq : q = 1 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (singletonHead_accept γ).mp (hγ.trans hq)
  subst γ
  have : i = 0 := by simp only [List.length_singleton] at hi; omega
  subst i
  decide +kernel

/-- The underlying instance has exactly one hole. -/
theorem uniqueBlocked_hole_iff (u t : Word Bool) :
    uniqueBlocked.toSS2.IsHole u t ↔ u = [] ∧ t = [false] := by
  constructor
  · intro h
    have hu : u = [] := by
      have hs := uniqueBlocked.toSS2.safeFrom_end h.1
      have hz : CoreExamples.emptyHeadDFA.run u = 0 := by
        change CoreExamples.emptyHeadDFA.run u ∉ ({1} : Finset (Fin 2)) at hs
        have hne : CoreExamples.emptyHeadDFA.run u ≠ 1 := by simpa using hs
        have hb := (CoreExamples.emptyHeadDFA.run u).isLt
        apply Fin.ext
        omega
      exact (CoreExamples.emptyHead_run_eq_zero u).mp hz
    subst u
    obtain ⟨s, hs, e, he, ha, hg⟩ := h.2.2.2
    have hdrop : t.drop e = [] := by simpa using ha.2.2.symm
    have hle : t.length ≤ e := by
      have hl := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil] at hl
      omega
    have hq : singletonHead.run (t.take e) = 1 :=
      (Prod.mk.inj (Finset.mem_singleton.mp hg)).2
    rw [List.take_of_length_le hle] at hq
    exact ⟨rfl, (singletonHead_accept t).mp hq⟩
  · rintro ⟨rfl, rfl⟩
    decide +kernel

/-- One strict self event eliminates the unique underlying SS2 hole. -/
theorem uniqueBlocked_no_hole : ¬ uniqueBlocked.HasHoleS := by
  rintro ⟨u, t, hh, hn⟩
  obtain ⟨rfl, rfl⟩ := (uniqueBlocked_hole_iff u t).mp hh
  exact (by decide +kernel : ¬ uniqueBlocked.NoSelf [false]) hn

/-- The concrete instance satisfies the hole and finite-head hypotheses. -/
theorem uniqueBlocked_nonvacuous : uniqueBlocked.FH ∧ uniqueBlocked.toSS2.HasHole ∧
    uniqueBlocked.SelfEvent [false] 0 1 ∧ ¬ uniqueBlocked.HasHoleS :=
  ⟨uniqueBlocked_fh, ⟨[], [false], by decide +kernel⟩,
    by decide +kernel, uniqueBlocked_no_hole⟩

/-- A signed mortal hole, obtained through the covariant regression bridge. -/
theorem mortal_hypotheses : CoreExamples.ternaryMortal.toSelf.FH ∧
    CoreExamples.ternaryMortal.toSelf.HasMortalHoleS :=
  ⟨CoreExamples.mortal_hypotheses.1, [], [],
    (SS2.isMortalHoleS_toSelf_iff _ _ _).mpr CoreExamples.ternary_mortal_hole⟩

/-- A thin safe component: zero may repeat, while one enters the bad sink. -/
def thinDFA : LDFA Bool (Fin 2) := ⟨0, fun q c => if c then 1 else q⟩

/-- A thin instance with an empty self guard. -/
def thin : SS2Self Bool (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  (CoreExamples.smallInstance thinDFA {1}).toSelf

/-- The concrete starting state is thin. -/
theorem thin_state : thin.Thin 0 := by
  have hv : thin.Viable 0 := by decide +kernel
  refine ⟨by decide, fun hm => hm.2 hv, ?_⟩
  rintro ⟨_, r, _, _, a, b, hab, ha, hb⟩
  cases a <;> cases b <;> simp_all [thin, SS2.toSelf, CoreExamples.smallInstance, thinDFA]

/-- The concrete safe stream has a bounded lasso representation. -/
theorem thin_lasso : thin.Lasso 0 (periodicStream [false]) := by
  exact ⟨[], [false], by decide, by decide, by decide, rfl, rfl⟩

/-- The concrete continuation is survivor-free. -/
theorem thin_survivorFree (u t : Word Bool) (ξ : ℕ → Bool) :
    thin.SurvivorFree u t ξ ∧ thin.SelfSurvivorFree t ξ := by
  constructor
  · intro s e he
    simpa [thin, SS2.toSelf, CoreExamples.smallInstance] using he.2.2
  · intro i j he
    simpa [thin, SS2.toSelf] using he.2.2.2

/-- The periodic interface has an actual thin, periodic pre-hole witness. -/
theorem thin_periodic_witness : thin.FH ∧ thin.Thin 0 ∧
    thin.Lasso 0 (periodicStream [false]) ∧
    (∃ p, 0 < p ∧ StreamPeriod (periodicStream [false]) p) ∧
    thin.IsPreHole [] [] ∧ thin.A.run [] = 0 ∧
    thin.SurvivorFree [] [] (periodicStream [false]) ∧
    thin.SelfSurvivorFree [] (periodicStream [false]) :=
  ⟨CoreExamples.smallInstance_fh _ _, thin_state, thin_lasso,
    ⟨1, by decide, periodicStream_period [false]⟩,
    by decide +kernel, rfl, thin_survivorFree _ _ _⟩

/-- This local periodic shortening premise holds with a nonempty family of inputs. -/
theorem thin_periodic_bound : thin.PurelyPeriodicShortPreHoleS 1 := by
  intro q ξ hq _ _ _
  have hne : q ≠ 1 := by simpa [thin, SS2.toSelf, CoreExamples.smallInstance] using hq.1
  have he : q = 0 := by
    apply Fin.ext
    have hb := q.isLt
    omega
  subst q
  exact ⟨[], [], by decide +kernel, rfl, (thin_survivorFree [] [] ξ).1,
    (thin_survivorFree [] [] ξ).2, by decide, by decide⟩

/-- The branching and hole premises also have a ternary witness. -/
theorem ternary_hypotheses : CoreExamples.ternaryBranch.toSelf.FH ∧
    CoreExamples.ternaryBranch.toSelf.HasHoleS ∧
    CoreExamples.ternaryBranch.toSelf.NonMortalCaseS :=
  ⟨CoreExamples.short_hypotheses.1,
    ⟨[], [], (SS2.isHoleS_toSelf_iff _ _ _).mpr CoreExamples.ternary_hole⟩,
    ⟨[], [], CoreExamples.ternary_preHole, Or.inl CoreExamples.ternary_branching⟩⟩

end DeciENSSE.Core.SS2SelfExamples
