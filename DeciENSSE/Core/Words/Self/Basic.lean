import Mathlib.Tactic.Tauto
import DeciENSSE.Core.Words.Transport
import DeciENSSE.Core.Words.NonMortal

/-! # Two-word instances with target self guards

Target self events extend the two-word hole condition. State transport preserves
the resulting hole and bound interfaces. Words are spine first, target second.

## Main declarations

- `SelfTwoWordInstance`
- `SelfTwoWordInstance.IsHole`
- `ShortHoleBoundSelf`
- `SelfTwoWordInstance.shortHoleBoundSelf_transport`
-/

namespace DeciENSSE.Core.Words.Self

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A two-word instance extended by a finite table of target self guards. -/
structure SelfTwoWordInstance (α : Type*) (SA SB SC SD : Type*) [Fintype SA] [Fintype SB]
    [Fintype SC] [Fintype SD] [DecidableEq SA] [DecidableEq SB]
    [DecidableEq SC] [DecidableEq SD] extends TwoWordInstance α SA SB SC SD where
  /-- Guarded pairs of target states for strict target self comparisons. -/
  SelfGuard : Finset (SB × SB)

namespace SelfTwoWordInstance
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
variable (I : SelfTwoWordInstance α SA SB SC SD)

/-- A guarded strict target comparison ending no later than the first rejection. -/
def SelfEvent (t : Word α) (i j : ℕ) : Prop :=
  i < j ∧ TwoWordInstance.Cross t t i j ∧ (∃ k ∈ I.J t, j ≤ k) ∧
    (I.B.atCut t i, I.B.atCut t j) ∈ I.SelfGuard

/-- Target self events are decidable at fixed cuts. -/
instance instDecidableSelfEvent (t : Word α) (i j : ℕ) : Decidable (I.SelfEvent t i j) := by
  unfold SelfEvent TwoWordInstance.Cross
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
def IsHole (u t : Word α) : Prop := I.toTwoWordInstance.IsHole u t ∧ I.NoSelf t

/-- The hole predicate with self events is decidable on a fixed word pair. -/
instance instDecidableIsHole (u t : Word α) : Decidable (I.IsHole u t) := by
  unfold IsHole
  infer_instance

/-- Existence of a hole with no target self events. -/
def HasHole : Prop := ∃ u t, I.IsHole u t

/-- A self-event-free hole with a mortal endpoint and a short rejected tail. -/
def IsMortalHole (u t : Word α) : Prop :=
  I.IsHole u t ∧ I.Mortal (I.A.run u) ∧
    ∃ j ∈ I.J t, t.length - j < Fintype.card SA

/-- The mortal-hole predicate with self events is decidable. -/
instance instDecidableIsMortalHole (u t : Word α) : Decidable (I.IsMortalHole u t) := by
  unfold IsMortalHole
  infer_instance

/-- Existence of a mortal hole with no target self events. -/
def HasMortalHole : Prop := ∃ u t, I.IsMortalHole u t

/-- A finite continuation breaks every current target self event. -/
def CompletesSelf (t θ : Word α) : Prop :=
  ∀ i j, I.SelfEvent t i j → ¬ TwoWordInstance.Keeps t t i j θ

/-- No current target self event survives the infinite continuation. -/
def SelfSurvivorFree (t : Word α) (ξ : ℕ → α) : Prop :=
  ∀ i j, I.SelfEvent t i j → ¬ TwoWordInstance.Survives t t i j ξ

/-- A branching pre-hole or a thin pre-hole with both survivor conditions. -/
def NonMortalCase : Prop := ∃ u t, I.IsPreHole u t ∧
  (I.Branching (I.A.run u) ∨ (I.Thin (I.A.run u) ∧
    ∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ))

/-- The periodic shortening premise retains both survivor conditions. -/
def PurelyPeriodicShortPreHole [Inhabited α] (K : ℕ) : Prop :=
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
    ¬ TwoWordInstance.Aligned t t i j := by
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
      I.SelfEvent t i j → ¬ TwoWordInstance.Keeps t t i j θ := by
  constructor
  · intro h i _ j _; exact h i j
  · intro h i j he
    exact h i (Finset.mem_range.mpr (by have := he.2.1.1; omega))
      j (Finset.mem_range.mpr (by have := he.2.1.2.1; omega)) he

/-- Whether a finite continuation breaks every self event is decidable. -/
instance instDecidableCompletesSelf (t θ : Word α) : Decidable (I.CompletesSelf t θ) := by
  letI (i j : ℕ) : Decidable (TwoWordInstance.Keeps t t i j θ) :=
    inferInstanceAs (Decidable (θ.IsPrefix (TwoWordInstance.overhang t t i j ++ θ)))
  exact decidable_of_iff _ (I.completesSelf_iff t θ).symm

omit [Fintype α] [DecidableEq α] in
/-- A mortal hole of an instance with self events is a mortal hole of the underlying instance
without self events. -/
theorem isMortalHole_iff (u t : Word α) :
    I.IsMortalHole u t ↔ I.toTwoWordInstance.IsMortalHole u t ∧ I.NoSelf t := by
  simp only [IsMortalHole, IsHole, TwoWordInstance.IsMortalHole]
  tauto

end SelfTwoWordInstance

/-- A state-count bound for holes with target self guards. -/
def ShortHoleBoundSelf (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
    I.ForcedHeads → I.HasHole → ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ B a b c d

/-- A state-count bound for the holes of the non-mortal cases, with self events.
Condition (FH) is not needed (`thm:nm-three-cases`). -/
def NonMortalShortHoleBoundSelf (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
    I.NonMortalCase → ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ B a b c d

/-- A state-count bound for mortal holes with target self guards. Condition
(FH) is not needed (`thm:mo-short`). -/
def MortalShortHoleBoundSelf (α : Type*) [Fintype α] [DecidableEq α] (B : HoleBound) : Prop :=
  ∀ a b c d, ∀ I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
    I.HasMortalHole → ∃ u t, I.IsMortalHole u t ∧ u.length + t.length ≤ B a b c d

/-- The three-case decomposition for instances with target self guards. -/
def ThreeCasesSelf (α : Type*) [Fintype α] [DecidableEq α] : Prop :=
  ∀ a b c d, ∀ I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
    I.ForcedHeads → (I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole)

/-- The maximum of a non-mortal and a mortal bound bounds the holes with self events. -/
theorem shortHoleBoundSelf_of_split {B₁ B₂ : HoleBound} (hc : ThreeCasesSelf α)
    (hn : NonMortalShortHoleBoundSelf α B₁) (hm : MortalShortHoleBoundSelf α B₂) :
    ShortHoleBoundSelf α (fun a b c d => max (B₁ a b c d) (B₂ a b c d)) := by
  intro a b c d I hfh hh
  rcases (hc a b c d I hfh).mp hh with h | h
  · obtain ⟨u, t, hu, hb⟩ := hn a b c d I h
    exact ⟨u, t, hu, hb.trans (le_max_left _ _)⟩
  · obtain ⟨u, t, hu, hb⟩ := hm a b c d I h
    exact ⟨u, t, hu.1, hb.trans (le_max_right _ _)⟩

end DeciENSSE.Core.Words.Self

namespace DeciENSSE.Core.Words.TwoWordInstance

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- The `TwoWordInstance.toSelf` embedding has no target self guards. -/
def toSelf (I : TwoWordInstance α SA SB SC SD) : (DeciENSSE.Core.Words.Self.SelfTwoWordInstance α)
  SA SB SC SD where
  toTwoWordInstance := I
  SelfGuard := ∅

omit [Fintype α] [DecidableEq α] in
/-- An instance with an empty self guard has no target self events. -/
@[simp] theorem noSelf_toSelf (I : TwoWordInstance α SA SB SC SD) (t : Word α) : I.toSelf.NoSelf t
  := by
  simp [DeciENSSE.Core.Words.Self.SelfTwoWordInstance.NoSelf,
    DeciENSSE.Core.Words.Self.SelfTwoWordInstance.SelfEvent, toSelf]

omit [Fintype α] [DecidableEq α] in
/-- Adding an empty self guard preserves the hole condition. -/
@[simp] theorem isHole_toSelf_iff (I : TwoWordInstance α SA SB SC SD) (u t : Word α) :
    I.toSelf.IsHole u t ↔ I.IsHole u t := by
  simp only [DeciENSSE.Core.Words.Self.SelfTwoWordInstance.IsHole, noSelf_toSelf, and_true]
  rfl

omit [Fintype α] [DecidableEq α] in
/-- Adding an empty self guard preserves the mortal-hole condition. -/
@[simp] theorem isMortalHole_toSelf_iff (I : TwoWordInstance α SA SB SC SD) (u t : Word α) :
    I.toSelf.IsMortalHole u t ↔ I.IsMortalHole u t := by
  rw [DeciENSSE.Core.Words.Self.SelfTwoWordInstance.isMortalHole_iff]
  simp only [noSelf_toSelf, and_true]
  rfl

end DeciENSSE.Core.Words.TwoWordInstance

namespace DeciENSSE.Core.Words.Self.SelfTwoWordInstance

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD TA TB TC TD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
  [Fintype TA] [Fintype TB] [Fintype TC] [Fintype TD]
  [DecidableEq TA] [DecidableEq TB] [DecidableEq TC] [DecidableEq TD]
variable (I : SelfTwoWordInstance α SA SB SC SD) (a : SA ≃ TA) (b : SB ≃ TB)
  (c : SC ≃ TC) (d : SD ≃ TD)

/-- Rename the underlying instance and both self-guard coordinates. -/
def rename : SelfTwoWordInstance α TA TB TC TD where
  toTwoWordInstance := I.toTwoWordInstance.rename a b c d
  SelfGuard := I.SelfGuard.map (Equiv.prodCongr b b).toEmbedding

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves target self events. -/
@[simp] theorem rename_selfEvent (t : Word α) (i j : ℕ) :
    (I.rename a b c d).SelfEvent t i j ↔ I.SelfEvent t i j := by
  unfold SelfEvent
  change (_ ∧ _ ∧ (∃ k ∈ (I.toTwoWordInstance.rename a b c d).J t, j ≤ k) ∧ _) ↔ _
  simp only [TwoWordInstance.rename_J]
  simp [rename, TwoWordInstance.rename]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves absence of self events. -/
@[simp] theorem rename_noSelf (t : Word α) :
    (I.rename a b c d).NoSelf t ↔ I.NoSelf t := by
  simp only [NoSelf, rename_selfEvent]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves holes with self events. -/
@[simp] theorem rename_isHole (u t : Word α) :
    (I.rename a b c d).IsHole u t ↔ I.IsHole u t := by
  exact and_congr (I.toTwoWordInstance.rename_isHole a b c d u t) (I.rename_noSelf a b c d t)

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves the existence of holes with self events. -/
@[simp] theorem rename_hasHole : (I.rename a b c d).HasHole ↔ I.HasHole := by
  simp only [HasHole, rename_isHole]

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves bounded holes with self events. -/
theorem rename_boundedHole (L : ℕ) :
    (∃ u t, (I.rename a b c d).IsHole u t ∧ u.length + t.length ≤ L) ↔
      ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ L := by simp

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves the forced target heads condition. -/
@[simp] theorem rename_forcedHeads : (I.rename a b c d).ForcedHeads ↔ I.ForcedHeads :=
  I.toTwoWordInstance.rename_forcedHeads a b c d

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves pre-holes. -/
@[simp] theorem rename_isPreHole (u t : Word α) :
    (I.rename a b c d).IsPreHole u t ↔ I.IsPreHole u t := by
  change (I.toTwoWordInstance.rename a b c d).IsPreHole u t ↔ I.toTwoWordInstance.IsPreHole u t
  simp only [TwoWordInstance.IsPreHole, TwoWordInstance.HasHeadEvent, TwoWordInstance.rename_J,
    TwoWordInstance.rename_headEvent, TwoWordInstance.rename_event]
  exact and_congr (I.toTwoWordInstance.rename_safeFrom a b c d I.A.start u) Iff.rfl

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves mortal holes with self events. -/
@[simp] theorem rename_isMortalHole (u t : Word α) :
    (I.rename a b c d).IsMortalHole u t ↔ I.IsMortalHole u t := by
  rw [isMortalHole_iff, isMortalHole_iff]
  exact and_congr (I.toTwoWordInstance.rename_isMortalHole a b c d u t) (I.rename_noSelf a b c d t)

omit [Fintype α] [DecidableEq α] in
/-- State renaming preserves the existence of mortal holes with self events. -/
@[simp] theorem rename_hasMortalHole :
    (I.rename a b c d).HasMortalHole ↔ I.HasMortalHole := by
  simp only [HasMortalHole, rename_isMortalHole]

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
theorem shortHoleBoundSelf_transport (B : HoleBound) (hB : ShortHoleBoundSelf α B)
    (hfh : I.ForcedHeads) (hh : I.HasHole) :
    ∃ u t, I.IsHole u t ∧ u.length + t.length ≤
      B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD) := by
  let a := Fintype.equivFin SA
  let b := Fintype.equivFin SB
  let c := Fintype.equivFin SC
  let d := Fintype.equivFin SD
  exact (rename_boundedHole I a b c d _).mp
    (hB _ _ _ _ (I.rename a b c d) ((rename_forcedHeads I a b c d).mpr hfh)
      ((rename_hasHole I a b c d).mpr hh))

end DeciENSSE.Core.Words.Self.SelfTwoWordInstance
