import DeciENSSE.Examples.Fixtures
import DeciENSSE.Examples.Words

/-! # Self-guarded examples

Concrete instances exercise holes, periodic continuations, and bounded searches.

## Main declarations

- `Self.PumpExamples`: periodic pumping examples with self guards.
- `Self.Examples`: mortal holes with target self events.
-/

namespace DeciENSSE.Core.Words.Self.SelfTwoWordInstanceExamples
open SelfTwoWordInstance

/-- The one-letter target has a self event at its two cuts. -/
theorem pending_event : pending.SelfEvent [false] 0 1 := by decide +kernel
/-- The pending example is a hole when self guards are ignored. -/
theorem pending_underlying_hole : pending.toTwoWordInstance.IsHole [false] [false] := by
  decide +kernel
/-- The pending self event blocks the self-aware hole. -/
theorem pending_blocked : ¬ pending.IsHole [false] [false] := by decide +kernel

/-- Appending the other letter breaks the pending self event. -/
theorem pending_breaks : pending.CompletesSelf [false] [true] := by decide +kernel
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

/-- The concrete instance satisfies the forced target heads condition. -/
theorem uniqueBlocked_forcedHeads : uniqueBlocked.ForcedHeads := by
  intro p q hp _ γ hγ i hi
  have hq : q = 1 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (singletonHead_accept γ).mp (hγ.trans hq)
  subst γ
  have : i = 0 := by simp only [List.length_singleton] at hi; omega
  subst i
  decide +kernel

/-- The underlying instance has exactly one hole. -/
theorem uniqueBlocked_hole_iff (u t : Word Bool) :
    uniqueBlocked.toTwoWordInstance.IsHole u t ↔ u = [] ∧ t = [false] := by
  constructor
  · intro h
    have hu : u = [] := by
      have hs := uniqueBlocked.toTwoWordInstance.safeFrom_end h.1
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

/-- One strict self event eliminates the unique underlying TwoWordInstance hole. -/
theorem uniqueBlocked_no_hole : ¬ uniqueBlocked.HasHole := by
  rintro ⟨u, t, hh, hn⟩
  obtain ⟨rfl, rfl⟩ := (uniqueBlocked_hole_iff u t).mp hh
  exact (by decide +kernel : ¬ uniqueBlocked.NoSelf [false]) hn

/-- The concrete instance satisfies the hole and forced target heads hypotheses. -/
theorem uniqueBlocked_nonvacuous : uniqueBlocked.ForcedHeads ∧
  uniqueBlocked.toTwoWordInstance.HasHole ∧
    uniqueBlocked.SelfEvent [false] 0 1 ∧ ¬ uniqueBlocked.HasHole :=
  ⟨uniqueBlocked_forcedHeads, ⟨[], [false], by decide +kernel⟩,
    by decide +kernel, uniqueBlocked_no_hole⟩

/-- A signed mortal hole obtained through `TwoWordInstance.toSelf`. -/
theorem mortal_hypotheses : CoreExamples.ternaryMortal.toSelf.ForcedHeads ∧
    CoreExamples.ternaryMortal.toSelf.HasMortalHole :=
  ⟨CoreExamples.mortal_hypotheses.1, [], [],
    (TwoWordInstance.isMortalHole_toSelf_iff _ _ _).mpr CoreExamples.ternary_mortal_hole⟩

/-- A thin safe component: zero may repeat, while one enters the bad sink. -/
def thinDFA : LDFA Bool (Fin 2) := ⟨0, fun q c => if c then 1 else q⟩

/-- A thin instance with an empty self guard. -/
def thin : SelfTwoWordInstance Bool (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  (CoreExamples.smallInstance thinDFA {1}).toSelf

/-- The concrete starting state is thin. -/
theorem thin_state : thin.Thin 0 := by
  have hv : thin.Viable 0 := by decide +kernel
  refine ⟨by decide, fun hm => hm.2 hv, ?_⟩
  rintro ⟨_, r, _, _, a, b, hab, ha, hb⟩
  cases a <;> cases b <;> simp_all [thin, TwoWordInstance.toSelf, CoreExamples.smallInstance,
    thinDFA]

/-- The concrete safe stream has a bounded lasso representation. -/
theorem thin_lasso : thin.Lasso 0 (periodicStream [false]) := by
  exact ⟨[], [false], by decide, by decide, by decide, rfl, rfl⟩

/-- The concrete continuation is survivor-free. -/
theorem thin_survivorFree (u t : Word Bool) (ξ : ℕ → Bool) :
    thin.SurvivorFree u t ξ ∧ thin.SelfSurvivorFree t ξ := by
  constructor
  · intro s e he
    simpa [thin, TwoWordInstance.toSelf, CoreExamples.smallInstance] using he.2.2
  · intro i j he
    simpa [thin, TwoWordInstance.toSelf] using he.2.2.2

/-- The periodic interface has an actual thin, periodic pre-hole witness. -/
theorem thin_periodic_witness : thin.ForcedHeads ∧ thin.Thin 0 ∧
    thin.Lasso 0 (periodicStream [false]) ∧
    (∃ p, 0 < p ∧ StreamPeriod (periodicStream [false]) p) ∧
    thin.IsPreHole [] [] ∧ thin.A.run [] = 0 ∧
    thin.SurvivorFree [] [] (periodicStream [false]) ∧
    thin.SelfSurvivorFree [] (periodicStream [false]) :=
  ⟨CoreExamples.smallInstance_forcedHeads _ _, thin_state, thin_lasso,
    ⟨1, by decide, periodicStream_period [false]⟩,
    by decide +kernel, rfl, thin_survivorFree _ _ _⟩

/-- This local periodic shortening premise holds with a nonempty family of inputs. -/
theorem thin_periodic_bound : thin.PurelyPeriodicShortPreHole 1 := by
  intro q ξ hq _ _ _
  have hne : q ≠ 1 := by simpa [thin, TwoWordInstance.toSelf, CoreExamples.smallInstance] using hq.1
  have he : q = 0 := by
    apply Fin.ext
    have hb := q.isLt
    omega
  subst q
  exact ⟨[], [], by decide +kernel, rfl, (thin_survivorFree [] [] ξ).1,
    (thin_survivorFree [] [] ξ).2, by decide, by decide⟩

/-- The branching and hole premises also have a ternary witness. -/
theorem ternary_hypotheses : CoreExamples.ternaryBranch.toSelf.ForcedHeads ∧
    CoreExamples.ternaryBranch.toSelf.HasHole ∧
    CoreExamples.ternaryBranch.toSelf.NonMortalCase :=
  ⟨CoreExamples.short_hypotheses.1,
    ⟨[], [], (TwoWordInstance.isHole_toSelf_iff _ _ _).mpr CoreExamples.ternary_hole⟩,
    ⟨[], [], CoreExamples.ternary_preHole, Or.inl CoreExamples.ternary_branching⟩⟩

end DeciENSSE.Core.Words.Self.SelfTwoWordInstanceExamples

namespace DeciENSSE.Core.Words.Self

namespace NonMortalExamples
open SelfTwoWordInstanceExamples

/-- A pending self event fires, and the branching bound completes it. -/
theorem branching_nonvacuous :
    pending.ForcedHeads ∧ pending.IsPreHole [false] [false] ∧ pending.SelfEvent [false] 0 1 ∧
      pending.Branching (pending.A.run [false]) ∧
      ∃ u t, pending.IsHole u t ∧ u.length + t.length ≤ 780 := by
  refine ⟨pending_forcedHeads, pending_preHole, pending_event, pending_branching, ?_⟩
  simpa using pending.short_branching_hole pending_preHole pending_branching

/-- The completion theorem breaks the pending self-event example. -/
theorem pending_completion : pending.IsHole [false, true] [false, true] := by
  apply pending.preHole_complete pending_preHole (θ := [true])
  · refine ⟨by decide +kernel, ?_⟩
    intro s e he
    exact (Finset.notMem_empty _ he.2.2).elim
  · exact pending_breaks

/-- The purely periodic premise and the associated survivor-free lasso are inhabited. -/
theorem periodic_nonvacuous :
    thin.ForcedHeads ∧ thin.PurelyPeriodicShortPreHole 1 ∧
      thin.Thin (thin.A.run []) ∧ thin.Lasso (thin.A.run []) (periodicStream [false]) ∧
      (∃ p, 0 < p ∧ StreamPeriod (periodicStream [false]) p) ∧
      thin.IsPreHole [] [] ∧ thin.SurvivorFree [] [] (periodicStream [false]) ∧
      thin.SelfSurvivorFree [] (periodicStream [false]) ∧
      ∃ u t, thin.IsHole u t ∧ u.length + t.length ≤ 8 := by
  obtain ⟨hfh, hthin, hl, hper, hp, _, hf, hg⟩ := thin_periodic_witness
  refine ⟨hfh, thin_periodic_bound, hthin, hl, hper, hp, hf, hg, ?_⟩
  simpa using thin.short_hole_of_lasso (K := 1) hp hl hf hg (by simp) (by simp)

/-- A thin lasso with a nonempty preperiod exercises the aperiodic short bound. -/
theorem aperiodic_nonvacuous :
    NonMortalExamples.aperiodicInstance.toSelf.ForcedHeads ∧
      NonMortalExamples.aperiodicInstance.toSelf.NonMortalCase ∧
      ∃ u t, NonMortalExamples.aperiodicInstance.toSelf.IsHole u t ∧
        u.length + t.length ≤ 294 := by
  let I := NonMortalExamples.aperiodicInstance.toSelf
  obtain ⟨hfh, hp, hthin, hl, hn⟩ := NonMortalExamples.aperiodic_trigger
  have hfree := I.toTwoWordInstance.aperiodic_survivorFree hp hn
  have hself := I.aperiodic_selfSurvivorFree (t := []) hn
  refine ⟨hfh, ⟨[], [], hp, Or.inr ⟨hthin, _, I.toTwoWordInstance.lasso_safe hl, hfree, hself⟩⟩, ?_⟩
  simpa [I] using I.short_aperiodic_hole hp hl hn

/-- The three-case interface includes the mortal instance. -/
theorem mortal_nonvacuous :
    CoreExamples.ternaryMortal.toSelf.ForcedHeads ∧
      CoreExamples.ternaryMortal.toSelf.HasMortalHole ∧
      CoreExamples.ternaryMortal.toSelf.HasHole := by
  obtain ⟨hf, hm⟩ := mortal_hypotheses
  exact ⟨hf, hm, (CoreExamples.ternaryMortal.toSelf.three_cases hf).mpr (Or.inr hm)⟩

/-- Both the branching premise and a genuine self obstruction occur. -/
theorem ternary_pending_hypotheses :
    ternaryPending.ForcedHeads ∧ ternaryPending.IsPreHole [1] [1] ∧
      ternaryPending.SelfEvent [1] 0 1 ∧ ¬ ternaryPending.IsHole [1] [1] ∧
      ternaryPending.Branching (ternaryPending.A.run [1]) ∧
      ¬ (ternaryPending.A.step 0 0 ∉ ternaryPending.Bad ∧
         ternaryPending.A.step 0 1 ∉ ternaryPending.Bad) := by
  exact ⟨ternaryPending_forcedHeads, by decide +kernel, by decide +kernel,
    by decide +kernel, CoreExamples.ternary_branching, by decide +kernel⟩

/-- The generic offset breaker works at every bound with safe letters one and two. -/
theorem ternary_breakerM (M : ℕ) :
    ∃ θ : Word (Fin 3), ternaryPending.SafeFrom 0 θ ∧ θ.length ≤ M + 6 ∧
      ∀ o : Word (Fin 3), o ≠ [] → o.length ≤ M → ¬ θ.IsPrefix (o ++ θ) := by
  simpa only [Fintype.card_fin] using
    ternaryPending.breakerM CoreExamples.ternary_branching M

/-- The self-aware branching bound applies with a nonempty ternary self guard. -/
theorem ternary_short_branching_hole :
    ∃ u t, ternaryPending.IsHole u t ∧ u.length + t.length ≤ 780 := by
  simpa using ternaryPending.short_branching_hole
    (u := [1]) (t := [1]) (by decide +kernel) CoreExamples.ternary_branching

end NonMortalExamples
end DeciENSSE.Core.Words.Self

namespace DeciENSSE.Core.Words.Self.PumpExamples
open SelfTwoWordInstance

/-- Non-vacuity with an actual pending self event and a periodic continuation
that destroys it. The nonempty self guard is checked by the stronger invariant. -/
theorem pending_pumpGood :
    SelfTwoWordInstanceExamples.pending.PumpGood (fun _ => true) [false] [false] := by
  apply (SelfTwoWordInstanceExamples.pending.pumpGood_iff _ _ _).mpr
  refine ⟨SelfTwoWordInstanceExamples.pending_preHole, ?_, ?_⟩
  · intro s e he
    simpa [SelfTwoWordInstanceExamples.pending] using he.2.2
  · apply (SelfTwoWordInstanceExamples.pending.selfSurvivorFree_iff
      SelfTwoWordInstanceExamples.pending_preHole.2.1).mpr
    intro i j hij hj heq
    have hi : i = 0 := by simp only [List.length_singleton] at hj; omega
    have hj' : j = 1 := by simp only [List.length_singleton] at hj; omega
    subst i j
    have h := congrFun heq 0
    simp [prepend] at h

/-- The stronger invariant has inputs of arbitrarily large total length. -/
theorem periodicGuard_long (k : ℕ) :
    NonMortalExamples.periodicGuardInstance.toSelf.PumpGood (fun _ => false)
      (true :: List.replicate k false) [] := by
  refine ⟨NonMortalExamples.periodicGuard_long k, ?_⟩
  intro i j hij hj
  simp only [List.length_nil] at hj
  omega

/-- An inhabited thin, purely periodic input shortens with the unchanged capacity 68. -/
theorem periodicGuard_long_short (k : ℕ) :
    ∃ u t, NonMortalExamples.periodicGuardInstance.toSelf.IsPreHole u t ∧
      NonMortalExamples.periodicGuardInstance.A.run u = 1 ∧
      NonMortalExamples.periodicGuardInstance.toSelf.SurvivorFree u t (fun _ => false) ∧
      NonMortalExamples.periodicGuardInstance.toSelf.SelfSurvivorFree t (fun _ => false) ∧
      u.length < 68 ∧ t.length < 68 := by
  let I := NonMortalExamples.periodicGuardInstance.toSelf
  obtain ⟨hph, hsf, hself⟩ := (I.pumpGood_iff _ _ _).mp (periodicGuard_long k)
  have hrun : I.A.run (true :: List.replicate k false) = 1 := by
    have h := NonMortalExamples.periodicGuard_atCut k (k + 1) (by omega)
    rwa [LDFA.atCut, List.take_of_length_le (by simp)] at h
  have h := I.purelyPeriodicShortPreHole_pump 1 (fun _ => false)
    NonMortalExamples.periodicGuard_thin NonMortalExamples.periodicGuard_lasso
    ⟨1, by decide, fun _ => rfl⟩ ⟨_, _, hph, hrun, hsf, hself⟩
  simpa [I, TwoWordInstance.toSelf, pumpCapacity] using h

/-- The ternary pump family also satisfies the self-aware invariant. -/
theorem ternaryPump_long (k : ℕ) :
    NonMortalExamples.ternaryPumpInstance.toSelf.PumpGood (fun _ => 1)
      (2 :: List.replicate k 1) [] := by
  refine ⟨NonMortalExamples.ternaryPump_long k, ?_⟩
  intro i j hij hj
  simp only [List.length_nil] at hj
  omega

/-- Arbitrarily long ternary inputs shorten with both survivor conditions and
the capacity 68 supplied by `TwoWordInstance.pumpSize_le`. -/
theorem ternaryPump_long_short (k : ℕ) :
    ∃ u t, NonMortalExamples.ternaryPumpInstance.toSelf.IsPreHole u t ∧
      NonMortalExamples.ternaryPumpInstance.A.run u = 1 ∧
      NonMortalExamples.ternaryPumpInstance.toSelf.SurvivorFree u t (fun _ => 1) ∧
      NonMortalExamples.ternaryPumpInstance.toSelf.SelfSurvivorFree t (fun _ => 1) ∧
      u.length < 68 ∧ t.length < 68 := by
  let I := NonMortalExamples.ternaryPumpInstance.toSelf
  have hp : LeastStreamPeriod (fun _ => (1 : Fin 3)) 1 :=
    ⟨by decide, fun _ => rfl, fun _ hq _ => hq⟩
  have hsize := TwoWordInstance.pumpSize_le (SA := Fin 3) (SB := Fin 1)
    (SA' := Fin 1) (SB' := Fin 2) (p := 1) (by decide)
  obtain ⟨u, t, hg, hrun, hu, ht⟩ := I.pumpGood_short hp hsize _ _ _
    le_rfl (ternaryPump_long k)
  obtain ⟨hph, hsf, hself⟩ := (I.pumpGood_iff _ _ _).mp hg
  have hend : I.A.run (2 :: List.replicate k 1) = 1 := by
    have h := NonMortalExamples.ternaryPump_atCut k (k + 1) (by omega)
    rwa [LDFA.atCut, List.take_of_length_le (by simp)] at h
  exact ⟨u, t, hph, hrun.trans hend, hsf, hself,
    by simpa [pumpCapacity] using hu, by simpa [pumpCapacity] using ht⟩

/-- Exercise the exact max-form endpoint at a ternary alphabet. -/
theorem ternary_max_capacity :
    NonMortalExamples.ternaryPumpInstance.toSelf.PurelyPeriodicShortPreHole 72 := by
  simpa [pumpCapacity] using
    (purelyPeriodicShortPreHole_capacity 3 1 1 2
      NonMortalExamples.ternaryPumpInstance.toSelf)

end DeciENSSE.Core.Words.Self.PumpExamples

namespace DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Words.Mortal
open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.RejectedTail DeciNSSE.LetteredHierarchy
open DeciENSSE.Anchored
namespace Examples
open DeciENSSE.Core.Words.Mortal.Examples

/-- The mortal chain, with a nonempty self guard that does not fire
on the witness: its only strict target pair has B states `(0,1)`. -/
def small : SelfTwoWordInstance Bool (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toTwoWordInstance := DeciENSSE.Core.Words.Mortal.Examples.small
  SelfGuard := {(1, 0)}

/-- The mortal witness has a nonempty self guard. -/
theorem small_selfGuard_nonempty : small.SelfGuard.Nonempty := by decide +kernel

/-- The mortal witness target has no self events. -/
theorem small_noSelf : small.NoSelf [true] := by decide +kernel

/-- The concrete binary word pair is a mortal self-aware hole. -/
theorem mortal_01_1 : small.IsMortalHole [false, true] [true] :=
  (small.isMortalHole_iff _ _).mpr
    ⟨DeciENSSE.Core.Words.Mortal.Examples.mortal_01_1, small_noSelf⟩

/-- The concrete instance satisfies the forced target heads condition. -/
theorem small_forcedHeads : small.ForcedHeads := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (DeciENSSE.Core.Words.CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- This instance has forced target heads and a mortal self-aware hole. -/
theorem small_hypotheses : small.ForcedHeads ∧ small.HasMortalHole :=
  ⟨small_forcedHeads, _, _, mortal_01_1⟩

/-- The separated binary witness is a reader hole with a head witness. -/
theorem piHole_01_sharp_1 : PiHole small (sepWord [false, true] [true]) :=
  (piHole_sep_iff small _ _).mpr mortal_01_1

/-- The concrete mortal witness satisfies the reader, head, and depth conditions. -/
theorem compression_input :
    (ofReader (reader small.toTwoWordInstance) (Adm small) (Rej small.toTwoWordInstance)).IsHole
      (sepWord [false, true] [true]) ∧
    HasPi small.toTwoWordInstance (sepWord [false, true] [true]) ∧
    DeciNSSE.HierarchyDepth.depth (sepWord [false, true] [true]) ≤ 167 := by
  simpa only [card_state, Fintype.card_fin] using
    mortal_compression_input small mortal_01_1

/-- Apply the complete theorem, without evaluating its astronomical bound. -/
theorem mortal_compressed :
    ∃ u t, small.IsMortalHole u t ∧
      u.length + t.length + 1 ≤ mortalHoleBound 4 2 2 2 := by
  simpa only [Fintype.card_fin] using exists_short_mortalHole small mortal_01_1

/-- Empty words and words with two separators cannot be positive reader holes. -/
theorem malformed_words :
    ¬ PosHole (ofReader (reader small.toTwoWordInstance) (Adm small) (Rej small.toTwoWordInstance))
      (baseChan (reader small.toTwoWordInstance) (Pi small.toTwoWordInstance) none) [] ∧
    ¬ PosHole (ofReader (reader small.toTwoWordInstance) (Adm small) (Rej small.toTwoWordInstance))
      (baseChan (reader small.toTwoWordInstance) (Pi small.toTwoWordInstance) none) [none, none]
        := by
  constructor <;> apply not_posHole_of_separator_count <;> decide

/-- Changing only the self guard blocks the same underlying mortal hole at `j = J`. -/
def blocked : SelfTwoWordInstance Bool (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toTwoWordInstance := DeciENSSE.Core.Words.Mortal.Examples.small
  SelfGuard := {(0, 1)}

/-- A changed self guard blocks the hole at the first rejected cut. -/
theorem blocked_at_first_rejection :
    blocked.J [true] = some 1 ∧ blocked.SelfEvent [true] 0 1 ∧
      ¬ blocked.IsMortalHole [false, true] [true] := by decide +kernel

/-- The blocked binary witness cannot give a reader hole with a head witness. -/
theorem blocked_no_piHole : ¬ PiHole blocked (sepWord [false, true] [true]) := by
  rw [piHole_sep_iff]
  exact blocked_at_first_rejection.2.2

/-- A ternary mortal witness with a nonempty self guard. -/
def ternarySmall : SelfTwoWordInstance (Fin 3) (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toTwoWordInstance := Mortal.Examples.ternarySmall
  SelfGuard := {(1, 0)}

/-- The ternary word pair is a mortal self-aware hole. -/
theorem ternary_mortal : ternarySmall.IsMortalHole [0, 2] [2] :=
  (ternarySmall.isMortalHole_iff _ _).mpr
    ⟨ternary_mortal_02_2, by decide +kernel⟩

/-- The mortal-bound premises hold, with an active third letter. -/
theorem ternary_hypotheses : ternarySmall.SelfGuard.Nonempty ∧
    ternarySmall.ForcedHeads ∧ ternarySmall.HasMortalHole := by
  refine ⟨by decide +kernel, ?_, _, _, ternary_mortal⟩
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- Elementary compression shortens the concrete mortal self-aware hole. -/
theorem ternary_compressed :
    ∃ u t, ternarySmall.IsMortalHole u t ∧
      u.length + t.length + 1 ≤ mortalHoleBound 4 2 2 2 := by
  simpa only [Fintype.card_fin] using exists_short_mortalHole ternarySmall ternary_mortal

/-- The self channel includes the first rejected cut over a ternary alphabet. -/
def ternaryBlocked : SelfTwoWordInstance (Fin 3) (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  toTwoWordInstance := Mortal.Examples.ternarySmall
  SelfGuard := {(0, 1)}

/-- The changed self guard also blocks the ternary witness at first rejection. -/
theorem ternary_blocked : ternaryBlocked.J [2] = some 1 ∧
    ternaryBlocked.SelfEvent [2] 0 1 ∧
    ¬ PiHole ternaryBlocked (sepWord [0, 2] [2]) := by
  rw [piHole_sep_iff]
  decide +kernel

end Examples
end DeciENSSE.Core.Words.Self

namespace DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Words.Mortal
/-- Apply the mortal bound to a ternary self-guard witness. -/
theorem Examples.ternary_public_bound :
    ∃ u t, ternarySmall.IsMortalHole u t ∧
      u.length + t.length ≤ mortalHoleBound 4 2 2 2 :=
  mortalShortHoleBoundSelf 4 2 2 2 ternarySmall
    ternary_hypotheses.2.1 ternary_hypotheses.2.2

end DeciENSSE.Core.Words.Self

namespace DeciENSSE.Core.Words.Self

namespace BoundExamples

/-- A genuine ternary hole with nonempty self guard exercises the assembled bound. -/
theorem ternary_bounded :
    ∃ u t, NonMortalExamples.ternaryPending.IsHole u t ∧
      u.length + t.length ≤ selfHoleBound 2 2 2 2 :=
  shortHoleBoundSelf (Fin 3) 2 2 2 2 _ NonMortalExamples.ternaryPending_forcedHeads
    ⟨[1, 2], [1, 2], NonMortalExamples.ternary_pending_completion⟩

/-- An empty-alphabet instance satisfies the forced target heads and hole hypotheses. -/
theorem empty_hypotheses : emptyInstance.ForcedHeads ∧ emptyInstance.IsHole [] [] :=
  ⟨CoreExamples.smallInstance_forcedHeads _ _, by decide +kernel⟩

end BoundExamples
end DeciENSSE.Core.Words.Self
