import DeciENSSE.Core.Words.TwoWordInstance

/-! # Renaming states and alphabets

State and alphabet equivalences preserve holes, forced target heads and mortality.

## Main declarations

- `TwoWordInstance.rename`
- `TwoWordInstance.mapAlpha`
-/

namespace DeciENSSE.Core.Words

variable {α : Type*}
namespace TwoWordInstance
variable {SA SB SC SD TA TB TC TD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
  [Fintype TA] [Fintype TB] [Fintype TC] [Fintype TD]
  [DecidableEq TA] [DecidableEq TB] [DecidableEq TC] [DecidableEq TD]
variable (I : TwoWordInstance α SA SB SC SD) (a : SA ≃ TA) (b : SB ≃ TB)
  (c : SC ≃ TC) (d : SD ≃ TD)

/-- Rename all four automata and all four finite tables. -/
def rename : TwoWordInstance α TA TB TC TD where
  A := I.A.rename a
  B := I.B.rename b
  A' := I.A'.rename c
  B' := I.B'.rename d
  Bad := Finset.univ.filter fun q => a.symm q ∈ I.Bad
  Rej := Finset.univ.filter fun q => b.symm q ∈ I.Rej
  Guard := Finset.univ.filter fun p => (a.symm p.1, b.symm p.2) ∈ I.Guard
  Head := Finset.univ.filter fun p => (c.symm p.1, d.symm p.2) ∈ I.Head

/-- State renaming preserves safety. -/
@[simp] theorem rename_safeFrom (q : SA) (w : Word α) :
    (I.rename a b c d).SafeFrom (a q) w ↔ I.SafeFrom q w := by
  simp [SafeFrom, rename]

/-- State renaming preserves the first rejected cut. -/
@[simp] theorem rename_J (t : Word α) : (I.rename a b c d).J t = I.J t := by
  simp [J, rename]

/-- State renaming preserves cross events. -/
@[simp] theorem rename_event (u t : Word α) (s e : ℕ) :
    (I.rename a b c d).Event u t s e ↔ I.Event u t s e := by
  simp only [Event, rename_J]
  simp [rename]

/-- State renaming preserves head events. -/
@[simp] theorem rename_headEvent (u t : Word α) (s e : ℕ) :
    (I.rename a b c d).HeadEvent u t s e ↔ I.HeadEvent u t s e := by
  simp [HeadEvent, rename]

/-- State renaming preserves holes. -/
@[simp] theorem rename_isHole (u t : Word α) :
    (I.rename a b c d).IsHole u t ↔ I.IsHole u t := by
  simp only [IsHole, HasHeadEvent, rename_J, rename_event, rename_headEvent]
  exact and_congr (rename_safeFrom I a b c d I.A.start u) Iff.rfl

/-- State renaming preserves hole existence. -/
@[simp] theorem rename_hasHole : (I.rename a b c d).HasHole ↔ I.HasHole := by
  simp [HasHole]

/-- State renaming preserves the forced target heads condition. -/
@[simp] theorem rename_forcedHeads : (I.rename a b c d).ForcedHeads ↔ I.ForcedHeads := by
  unfold ForcedHeads
  constructor
  · intro h p q hp hr γ hγ i hi
    have ht := h (c p) (d q) (by simpa [rename] using hp)
      ((LDFA.rename_reachable I.A' c p).mpr hr) γ
      (by simpa [rename] using congrArg d hγ) i hi
    simpa [rename] using ht
  · intro h p q hp hr γ hγ i hi
    obtain ⟨p, rfl⟩ := c.surjective p
    obtain ⟨q, rfl⟩ := d.surjective q
    have ht := h p q (by simpa [rename] using hp)
      ((LDFA.rename_reachable I.A' c p).mp hr) γ
      (by simpa [rename] using hγ) i hi
    simpa [rename] using ht

/-- State renaming preserves infinite safety. -/
@[simp] theorem rename_infiniteSafe (q : SA) (ξ : ℕ → α) :
    (I.rename a b c d).InfiniteSafe (a q) ξ ↔ I.InfiniteSafe q ξ := by
  simp [InfiniteSafe, rename]

/-- State renaming preserves mortal states. -/
@[simp] theorem rename_mortal (q : SA) :
    (I.rename a b c d).Mortal (a q) ↔ I.Mortal q := by
  simp only [mortal_iff, rename_infiniteSafe]
  simp [rename]

/-- State renaming preserves mortal holes. -/
@[simp] theorem rename_isMortalHole (u t : Word α) :
    (I.rename a b c d).IsMortalHole u t ↔ I.IsMortalHole u t := by
  simp only [IsMortalHole, rename_isHole, rename_J]
  change (I.IsHole u t ∧ (I.rename a b c d).Mortal ((I.A.rename a).run u) ∧ _) ↔ _
  rw [LDFA.rename_run, rename_mortal, Fintype.card_congr a]

/-- State renaming preserves mortal-hole existence. -/
@[simp] theorem rename_hasMortalHole :
    (I.rename a b c d).HasMortalHole ↔ I.HasMortalHole := by simp [HasMortalHole]

end TwoWordInstance

namespace LDFA
variable {β S : Type*}

/-- Change the alphabet along an explicit equivalence; states are unchanged. -/
def mapAlpha (M : LDFA α S) (e : α ≃ β) : LDFA β S where
  start := M.start
  step q c := M.step q (e.symm c)

/-- Alphabet transport preserves runs from a given state. -/
@[simp] theorem mapAlpha_runFrom (M : LDFA α S) (e : α ≃ β) (q : S) (w : Word α) :
    (M.mapAlpha e).runFrom q (w.map e) = M.runFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih => simpa [runFrom, mapAlpha] using ih (M.step q c)

/-- Alphabet transport preserves runs. -/
@[simp] theorem mapAlpha_run (M : LDFA α S) (e : α ≃ β) (w : Word α) :
    (M.mapAlpha e).run (w.map e) = M.run w := mapAlpha_runFrom M e M.start w

/-- Alphabet transport preserves states at cuts. -/
@[simp] theorem mapAlpha_atCut (M : LDFA α S) (e : α ≃ β) (w : Word α) (s : ℕ) :
    (M.mapAlpha e).atCut (w.map e) s = M.atCut w s := by
  simp only [atCut, ← List.map_take, mapAlpha_run]

/-- Alphabet transport preserves reachability. -/
@[simp] theorem mapAlpha_reachable (M : LDFA α S) (e : α ≃ β) (q : S) :
    (M.mapAlpha e).Reachable q ↔ M.Reachable q := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.map e.symm, ?_⟩
    simpa using (mapAlpha_run M e (w.map e.symm)).symm.trans (by simpa using hw)
  · rintro ⟨w, hw⟩
    exact ⟨w.map e, (mapAlpha_run M e w).trans hw⟩

/-- Alphabet transport preserves stream runs. -/
@[simp] theorem mapAlpha_streamRun (M : LDFA α S) (e : α ≃ β)
    (q : S) (ξ : ℕ → α) (n : ℕ) :
    (M.mapAlpha e).streamRun q (e ∘ ξ) n = M.streamRun q ξ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [streamRun, ih]
    simp [mapAlpha]
end LDFA

namespace TwoWordInstance
variable {β SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
variable (I : TwoWordInstance α SA SB SC SD) (e : α ≃ β)

/-- Transport the alphabet of all four automata, keeping every finite table. -/
def mapAlpha : TwoWordInstance β SA SB SC SD where
  A := I.A.mapAlpha e
  B := I.B.mapAlpha e
  A' := I.A'.mapAlpha e
  B' := I.B'.mapAlpha e
  Bad := I.Bad
  Rej := I.Rej
  Guard := I.Guard
  Head := I.Head

/-- Alphabet transport preserves safety. -/
@[simp] theorem safeFrom_mapAlpha (q : SA) (w : Word α) :
    (I.mapAlpha e).SafeFrom q (w.map e) ↔ I.SafeFrom q w := by
  simp only [SafeFrom, List.length_map, ← List.map_take, mapAlpha, LDFA.mapAlpha_runFrom]

/-- Alphabet transport preserves the first rejected cut. -/
@[simp] theorem J_mapAlpha (t : Word α) : (I.mapAlpha e).J (t.map e) = I.J t := by
  simp only [J, List.length_map, mapAlpha, LDFA.mapAlpha_atCut]

/-- Alphabet transport preserves cross comparisons. -/
@[simp] theorem cross_mapAlpha (u t : Word α) (s k : ℕ) :
    Cross (u.map e) (t.map e) s k ↔ Cross u t s k := by
  simp only [Cross, List.length_map, ← List.map_drop]
  constructor
  · rintro ⟨hs, hk, h⟩
    exact ⟨hs, hk, by simpa using h.map e.symm⟩
  · rintro ⟨hs, hk, h⟩
    exact ⟨hs, hk, h.map e⟩

/-- Alphabet transport preserves aligned comparisons. -/
@[simp] theorem aligned_mapAlpha (u t : Word α) (s k : ℕ) :
    Aligned (u.map e) (t.map e) s k ↔ Aligned u t s k := by
  simp only [Aligned, List.length_map, ← List.map_drop, List.map_inj_right e.injective]

/-- Alphabet transport preserves cross events. -/
@[simp] theorem event_mapAlpha (u t : Word α) (s k : ℕ) :
    (I.mapAlpha e).Event (u.map e) (t.map e) s k ↔ I.Event u t s k := by
  simp only [Event, cross_mapAlpha, J_mapAlpha]
  simp only [mapAlpha, LDFA.mapAlpha_atCut]

/-- Alphabet transport preserves head events. -/
@[simp] theorem headEvent_mapAlpha (u t : Word α) (s k : ℕ) :
    (I.mapAlpha e).HeadEvent (u.map e) (t.map e) s k ↔ I.HeadEvent u t s k := by
  simp only [HeadEvent, aligned_mapAlpha, mapAlpha, LDFA.mapAlpha_atCut]

/-- Alphabet transport preserves holes. -/
@[simp] theorem isHole_mapAlpha (u t : Word α) :
    (I.mapAlpha e).IsHole (u.map e) (t.map e) ↔ I.IsHole u t := by
  simp only [IsHole, HasHeadEvent, List.length_map, J_mapAlpha, event_mapAlpha,
    headEvent_mapAlpha]
  exact and_congr (safeFrom_mapAlpha I e I.A.start u) Iff.rfl

/-- Alphabet transport preserves hole existence. -/
@[simp] theorem hasHole_mapAlpha : (I.mapAlpha e).HasHole ↔ I.HasHole := by
  constructor
  · rintro ⟨u, t, h⟩
    exact ⟨u.map e.symm, t.map e.symm,
      (isHole_mapAlpha I e _ _).mp (by simpa using h)⟩
  · rintro ⟨u, t, h⟩
    exact ⟨u.map e, t.map e, (isHole_mapAlpha I e u t).mpr h⟩

/-- Alphabet transport preserves the forced target heads condition. -/
@[simp] theorem forcedHeads_mapAlpha : (I.mapAlpha e).ForcedHeads ↔ I.ForcedHeads := by
  unfold ForcedHeads
  constructor
  · intro h p q hp hr γ hγ i hi
    have ht := h p q hp ((LDFA.mapAlpha_reachable I.A' e p).mpr hr) (γ.map e)
      (by simpa [mapAlpha] using hγ) i (by simpa using hi)
    simpa [mapAlpha] using ht
  · intro h p q hp hr γ hγ i hi
    obtain ⟨γ, rfl⟩ := (List.map_surjective_iff.mpr e.surjective) γ
    have ht := h p q hp ((LDFA.mapAlpha_reachable I.A' e p).mp hr) γ
      (by simpa only [mapAlpha, LDFA.mapAlpha_run] using hγ)
      i (by simpa only [List.length_map] using hi)
    simpa only [mapAlpha, LDFA.mapAlpha_atCut] using ht

end TwoWordInstance

end DeciENSSE.Core.Words
