import DeciENSSE.Examples.Fixtures
import DeciENSSE.Core.Words.Bound
import DeciENSSE.Core.Words.Periodic

/-! # Two-word examples

Concrete instances exercise holes, periodic continuations, and bounded searches.

## Main declarations

- `NonMortalExamples.periodicGuard_long`: arbitrarily long periodic pre-holes.
- `Mortal.Examples.small`: a mortal-hole fixture.
-/

namespace DeciENSSE.Core.Words

namespace NonMortalExamples

open CoreExamples

/-- A concrete safe breaker: follow the one-cycle three times, then take two. -/
theorem ternary_breaker_word :
    ternaryBranch.SafeFrom 0 [1, 1, 1, 2] ∧
      ([1, 1, 1, 2] : Word (Fin 3)).length ≤ 7 ∧
      ∀ s e, TwoWordInstance.Cross ([1] : Word (Fin 3)) [] s e →
        ¬ TwoWordInstance.Aligned ([1] : Word (Fin 3)) [] s e →
        ¬ TwoWordInstance.Keeps ([1] : Word (Fin 3)) [] s e [1, 1, 1, 2] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro s e hc ha
  have hs : s ≤ 1 := hc.1
  have he : e = 0 := by have := hc.2.1; simp only [List.length_nil] at this; omega
  subst e
  interval_cases s
  · unfold TwoWordInstance.Keeps TwoWordInstance.overhang
    decide +kernel
  · exact (ha (by unfold TwoWordInstance.Aligned; decide +kernel)).elim

/-- This instance has a non-aligned cross comparison to break. -/
theorem ternary_cross :
    TwoWordInstance.Cross ([1] : Word (Fin 3)) [] 0 0 ∧
      ¬ TwoWordInstance.Aligned ([1] : Word (Fin 3)) [] 0 0 := by
  unfold TwoWordInstance.Cross TwoWordInstance.Aligned
  decide +kernel

/-- Exercise the departure theorem itself with a third-alphabet letter. -/
theorem ternary_departure :
    ¬ IsStreamPrefix ([1, 1, 1, 2] : Word (Fin 3)) (periodicStream [1]) := by
  exact periodic_departure_breaks (o := [1]) (l := [1])
    (by decide +kernel) (by decide +kernel) [] 3 (by decide +kernel)
    2 (by decide +kernel)

end NonMortalExamples
end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words

namespace NonMortalExamples

/-- A safe zero-loop with the other letter entering a bad sink. -/
def thinDFA : LDFA Bool (Fin 2) := ⟨0, fun q c => if q = 0 ∧ c = false then 0 else 1⟩

/-- A two-state thin instance with a zero-loop and a bad sink. -/
def thinInstance : TwoWordInstance Bool (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance thinDFA {1}

/-- The concrete starting state is thin. -/
theorem thin_state : thinInstance.Thin 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro hm
    apply hm.2
    refine ⟨{0}, by simp, ?_⟩
    intro r hr
    have hr' : r = 0 := Finset.mem_singleton.mp hr
    subst r
    exact ⟨by decide, false, by decide⟩
  · rintro ⟨_, r, _, _, a, b, hab, ha, hb⟩
    have hletter (c : Bool) (hc : thinInstance.A.step r c ∉ thinInstance.Bad) :
        c = false := by
      cases c with
      | false => rfl
      | true => simp [thinInstance, CoreExamples.smallInstance, thinDFA] at hc
    exact hab ((hletter a ha).trans (hletter b hb).symm)

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem thin_preHole : thinInstance.IsPreHole [] [] := by decide +kernel

/-- The concrete safe stream has a bounded lasso representation. -/
theorem thin_lasso : thinInstance.Lasso 0 (periodicStream [false]) := by
  refine ⟨[], [false], by decide, by decide, by decide, rfl, ?_⟩
  simp

/-- The concrete continuation is survivor-free. -/
theorem thin_survivorFree : thinInstance.SurvivorFree [] [] (periodicStream [false]) := by
  intro s e he
  exact (Finset.notMem_empty _ he.2.2).elim

/-- The thin instance satisfies the non-mortal case. -/
theorem thin_case : thinInstance.ForcedHeads ∧ thinInstance.NonMortalCase := by
  refine ⟨CoreExamples.smallInstance_forcedHeads _ _, [], [], thin_preHole, Or.inr ?_⟩
  exact ⟨thin_state, periodicStream [false], thinInstance.lasso_safe thin_lasso, thin_survivorFree⟩

/-- The finite lasso enumeration contains a safe lasso. -/
theorem thin_enumeration_nonempty : (thinInstance.lassoPairs 0).Nonempty := by decide +kernel

/-- An empty completion cannot remove the pending event in this instance. -/
theorem completes_nonempty : thinInstance.Completes [] [] [] := by
  refine ⟨by decide, ?_⟩
  intro s e he
  exact (Finset.notMem_empty _ he.2.2).elim

/-- A least stream period is positive. -/
theorem leastPeriod_nonempty : LeastStreamPeriod (fun _ => false) 1 := by
  exact ⟨by decide, fun _ => rfl, fun q hq _ => hq⟩

/-- The executable branching test finds the two safe nonzero ternary letters. -/
theorem ternary_branching_decide :
    @decide _ (CoreExamples.ternaryBranch.branchingDecidable 0) = true := by
  decide +kernel

/-- A single safe state over the unary alphabet. -/
def unaryInstance : TwoWordInstance (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance CoreExamples.oneDFA ∅

/-- The concrete starting state is thin. -/
theorem unary_thin : unaryInstance.Thin 0 := by
  exact @of_decide_eq_true _ (unaryInstance.thinDecidable 0) (by decide +kernel)

/-- The finite enumeration contains exactly the presentation of `0^ω`. -/
theorem unary_lassoPairs : unaryInstance.lassoPairs 0 = {([], [0])} := by
  decide +kernel

/-- The only safe unary stream is the constant stream. -/
theorem unary_safe_iff (ξ : ℕ → Fin 1) :
    unaryInstance.InfiniteSafe 0 ξ ↔ ξ = periodicStream [0] := by
  rw [unaryInstance.thin_lassoPairs_iff unary_thin, unary_lassoPairs]
  simp

end NonMortalExamples
end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words

namespace NonMortalExamples

/-- Its periodic branch has an actual trigger, so the preceding example
is not satisfied merely because there are no thin periodic witnesses. -/
theorem thin_periodic_trigger :
    thinInstance.Thin 0 ∧ thinInstance.Lasso 0 (periodicStream [false]) ∧
    (∃ p, 0 < p ∧ StreamPeriod (periodicStream [false]) p) ∧
    (∃ u t, thinInstance.IsPreHole u t ∧ thinInstance.A.run u = 0 ∧
      thinInstance.SurvivorFree u t (periodicStream [false])) := by
  exact ⟨thin_state, thin_lasso, ⟨1, by decide, periodicStream_period [false]⟩,
    [], [], thin_preHole, rfl, thin_survivorFree⟩

/-- Positive recognition example for the pre-hole graph. -/
theorem thin_preHole_accepted : (thinInstance.preHoleGraph {0}).Accepts [] [] :=
  thinInstance.preHoleGraph_complete {0} thin_preHole (by decide)

/-- One transient letter followed by the zero-loop; all other moves are bad. -/
def aperiodicDFA : LDFA Bool (Fin 3) :=
  ⟨0, fun q c => if (q = 0 ∧ c = true) ∨ (q = 1 ∧ c = false) then 1 else 2⟩

/-- An instance whose safe stream has a one-letter stem followed by a zero-loop. -/
def aperiodicInstance : TwoWordInstance Bool (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance aperiodicDFA {2}

/-- The concrete starting state is thin. -/
theorem aperiodic_thin : aperiodicInstance.Thin 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro h
    exact h.2 (by decide +kernel : aperiodicInstance.Viable 0)
  · rintro ⟨_, r, _, _, a, b, hab, ha, hb⟩
    fin_cases r <;> cases a <;> cases b <;>
      simp_all [aperiodicInstance, CoreExamples.smallInstance, aperiodicDFA]

/-- The concrete safe stream has a bounded lasso representation. -/
theorem aperiodic_lasso :
    aperiodicInstance.Lasso 0 (prepend [true] (periodicStream [false])) := by
  exact ⟨[true], [false], by decide, by decide, by decide, rfl, rfl⟩

/-- The concrete lasso stream has no positive period. -/
theorem aperiodic_no_period :
    ¬ ∃ p, 0 < p ∧ StreamPeriod (prepend [true] (periodicStream [false])) p := by
  rintro ⟨p, hp, h⟩
  have he := h 0
  simp [prepend, periodicStream, Nat.mod_one, show ¬ p < 1 by omega] at he

/-- An actual witness of the aperiodic thin branch, with ForcedHeads. -/
theorem aperiodic_trigger :
    aperiodicInstance.ForcedHeads ∧ aperiodicInstance.IsPreHole [] [] ∧
      aperiodicInstance.Thin (aperiodicInstance.A.run []) ∧
      aperiodicInstance.Lasso (aperiodicInstance.A.run [])
        (prepend [true] (periodicStream [false])) ∧
      ¬ ∃ p, 0 < p ∧ StreamPeriod (prepend [true] (periodicStream [false])) p := by
  exact ⟨CoreExamples.smallInstance_forcedHeads _ _, by decide +kernel,
    aperiodic_thin, aperiodic_lasso, aperiodic_no_period⟩

/-- The graph reads a genuinely ternary safe spine and retains its endpoint. -/
theorem ternary_preHole_accepted :
    (CoreExamples.ternaryBranch.preHoleGraph {0}).Accepts [1, 2] [] := by
  exact CoreExamples.ternaryBranch.preHoleGraph_complete {0}
    (by decide +kernel) (by decide +kernel)

/-- Unsafe spines, premature rejection, and a wrong endpoint are all rejected. -/
theorem ternary_preHole_rejected :
    ¬ (CoreExamples.ternaryBranch.preHoleGraph {0}).Accepts [0] [] ∧
    ¬ (CoreExamples.ternaryBranch.preHoleGraph {0}).Accepts [] [1] ∧
    ¬ (CoreExamples.ternaryBranch.preHoleGraph {1}).Accepts [1, 2] [] := by
  simp only [CoreExamples.ternaryBranch.preHoleGraph_correct]
  decide +kernel

/-- Both stored bits persist on equal letters and reset on unequal letters.
The freshly reached head and guard pairs in this example are absent. -/
theorem ternary_preBoth_flags :
    let I := CoreExamples.ternaryBranch
    let p := { I.preNode [] [] 0 with gd := true }
    (I.preBoth p 1 1).hd = true ∧ (I.preBoth p 1 1).gd = true ∧
    (I.preBoth p 1 2).hd = false ∧ (I.preBoth p 1 2).gd = false := by
  decide +kernel

/-- A ternary instance with exactly one safe outgoing letter at its live state. -/
def ternaryThinInstance : TwoWordInstance (Fin 3) (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance ⟨0, fun q c => if q = 0 ∧ c = 1 then 0 else 1⟩ {1}

/-- The periodic interface has an actual ternary trigger, including ForcedHeads. -/
theorem ternary_periodic_trigger :
    ternaryThinInstance.ForcedHeads ∧ ternaryThinInstance.Thin 0 ∧
    ternaryThinInstance.Lasso 0 (periodicStream [1]) ∧
    (∃ p, 0 < p ∧ StreamPeriod (periodicStream ([1] : Word (Fin 3))) p) ∧
    (∃ u t, ternaryThinInstance.IsPreHole u t ∧ ternaryThinInstance.A.run u = 0 ∧
      ternaryThinInstance.SurvivorFree u t (periodicStream [1])) := by
  refine ⟨CoreExamples.smallInstance_forcedHeads _ _, ?_, ?_,
    ⟨1, by decide, periodicStream_period [1]⟩, [], [], by decide +kernel, rfl, ?_⟩
  · exact @of_decide_eq_true _ (ternaryThinInstance.thinDecidable 0) (by decide +kernel)
  · refine ⟨[], [1], by decide, by decide, by decide, rfl, ?_⟩
    simp
  · intro s e he
    exact (Finset.notMem_empty _ he.2.2).elim

/-- Empty alphabets still admit the finite pre-hole search. -/
def emptyAlphabetInstance : TwoWordInstance (Fin 0) (Fin 1) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance CoreExamples.oneDFA ∅

/-- Execute both outcomes of the search without requiring an inhabited alphabet. -/
theorem emptyAlphabet_search :
    @decide _ (emptyAlphabetInstance.preHoleExistsDecidable {0}) = true ∧
    @decide _ (emptyAlphabetInstance.preHoleExistsDecidable ∅) = false := by
  decide +kernel

end NonMortalExamples
end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words

namespace NonMortalExamples

/-- Both first letters enter a thin zero-loop. The guard at the initial
spine state distinguishes the overhangs `[false]` and `[true]`. -/
def periodicGuardDFA : LDFA Bool (Fin 3) :=
  ⟨0, fun q c => if q = 0 ∨ (q = 1 ∧ c = false) then 1 else 2⟩

/-- A thin instance whose initial guard distinguishes the two overhang letters. -/
def periodicGuardInstance : TwoWordInstance Bool (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
  { CoreExamples.smallInstance periodicGuardDFA {2} with Guard := {(0, 0)} }

/-- The concrete starting state is thin. -/
theorem periodicGuard_thin : periodicGuardInstance.Thin 1 := by
  exact @of_decide_eq_true _ (periodicGuardInstance.thinDecidable 1) (by decide +kernel)

/-- The concrete safe stream has a bounded lasso representation. -/
theorem periodicGuard_lasso : periodicGuardInstance.Lasso 1 (fun _ => false) := by
  refine ⟨[], [false], by decide, by decide, by decide, rfl, ?_⟩
  funext i
  simp [prepend, periodicStream, Nat.mod_one]

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem periodicGuard_preHoles :
    periodicGuardInstance.IsPreHole [false] [] ∧
      periodicGuardInstance.IsPreHole [true] [] := by decide +kernel

/-- A zero residue is not by itself sufficient for survival. -/
theorem periodicGuard_true_survivorFree :
    periodicGuardInstance.SurvivorFree [true] [] (fun _ => false) := by
  rw [periodicGuardInstance.survivorFree_iff_suffix_guard (by decide)]
  intro s hs e he _ heq
  have he' : e = 0 := by simpa using he
  subst e
  have hs' : s ≤ 1 := by simpa using hs
  interval_cases s
  · have hh := congrFun heq 0
    simp [prepend] at hh
  · decide +kernel

/-- The zero overhang event survives the constant-zero stream. -/
theorem periodicGuard_false_survivor :
    periodicGuardInstance.Event [false] [] 0 0 ∧
      TwoWordInstance.Survives [false] [] 0 0 (fun _ => false) := by
  refine ⟨by unfold TwoWordInstance.Event TwoWordInstance.Cross; decide +kernel, ?_⟩
  apply (TwoWordInstance.survives_iff_overhang_fixed (by simp [TwoWordInstance.Cross] :
    TwoWordInstance.Cross [false] [] 0 0) _).mpr
  funext i
  simp [TwoWordInstance.overhang, prepend]

/-- Maximal periodic ends have witnesses even when the rest is nonempty. -/
theorem periodicSplit_nonempty_rest :
    PeriodicSplit (fun _ => false) 1 [true, false, false] 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        simp [prepend, show ¬ i + 1 + 1 < 2 by omega,
          show ¬ i + 1 + 1 + 1 < 2 by omega]
  · intro s hs h
    have hs' : s = 0 := by omega
    subst s
    have hh := h 0
    simp [prepend] at hh

/-- A third letter can form the nonperiodic rest before a constant tail. -/
theorem periodicSplit_ternary_rest :
    PeriodicSplit (fun _ => (0 : Fin 3)) 1 [2, 0, 0] 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        simp [prepend, show ¬ i + 1 + 1 < 2 by omega,
          show ¬ i + 1 + 1 + 1 < 2 by omega]
  · intro s hs h
    have hs' : s = 0 := by omega
    subst s
    have hh := h 0
    simp [prepend] at hh

/-- The guard at depth zero is included, even at zero offset. -/
theorem periodicForbidden_aligned :
    (0 : Fin 3) ∈ periodicGuardInstance.periodicForbidden [] 0 (0 : Fin 1) := by
  decide +kernel

/-- A deeper target cut enters its own residue only when it is reached. -/
theorem periodicForbidden_depth_cutoff :
    periodicGuardInstance.periodicForbidden [false] 0 (1 : Fin 2) = ∅ ∧
      periodicGuardInstance.periodicForbidden [false] 1 (1 : Fin 2) = {0} := by
  decide +kernel

/-- The surviving false overhang is rejected by the semantic periodic test. -/
theorem periodicGuard_false_forbidden :
    ¬ (∀ k ≤ ([false] : Word Bool).length,
      periodicGuardInstance.A.atCut [false] (1 - k) ∉
        periodicGuardInstance.periodicForbidden [] (min k 0) (0 : Fin 1)) := by
  intro h
  exact h 1 (by decide) (by decide +kernel)

end NonMortalExamples
end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words

namespace NonMortalExamples

/-- The concrete reader stays in state one along the periodic word. -/
theorem periodicGuard_runFrom_one (k : ℕ) :
    periodicGuardInstance.A.runFrom 1 (List.replicate k false) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    change periodicGuardInstance.A.runFrom (periodicGuardInstance.A.step 1 false) _ = 1
    rw [show periodicGuardInstance.A.step 1 false = 1 by decide]
    exact ih

/-- The concrete reader states at each cut have this explicit form. -/
theorem periodicGuard_atCut (k s : ℕ) (hs : 1 ≤ s) :
    periodicGuardInstance.A.atCut (true :: List.replicate k false) s = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hs
  change periodicGuardInstance.A.runFrom periodicGuardInstance.A.start
    ((true :: List.replicate k false).take (s + 1)) = 1
  rw [List.take_succ_cons, List.take_replicate]
  change periodicGuardInstance.A.runFrom (periodicGuardInstance.A.step 0 true) _ = 1
  rw [show periodicGuardInstance.A.step 0 true = 1 by decide]
  exact periodicGuard_runFrom_one _

/-- Survivor-free pre-holes of every length, with a nonempty guard: the
pumping induction has arbitrarily long inputs. -/
theorem periodicGuard_long (k : ℕ) :
    periodicGuardInstance.PumpGood (fun _ => false) (true :: List.replicate k false) [] := by
  refine ⟨?_, ?_, by decide, ?_, ?_⟩
  · rw [TwoWordInstance.safeFrom_iff]
    intro s _
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · rw [List.take_zero]
      decide
    · change periodicGuardInstance.A.atCut _ s ∉ _
      rw [periodicGuard_atCut k s hpos]
      decide
  · intro i hi
    simp at hi
  · refine ⟨k + 1, by simp, 0, by simp, ⟨by simp, by simp, by simp⟩, ?_⟩
    rw [Fin.fin_one_eq_zero (periodicGuardInstance.A'.atCut _ _)]
    decide
  · intro s _ e he _ hsuf
    have he0 : e = 0 := by simpa using he
    subst he0
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h0 := congrFun hsuf 0
      simp [prepend] at h0
    · rw [periodicGuard_atCut k s hpos]
      decide

/-- All initial letters enter state one; only letter one then stays safe. -/
def ternaryPumpInstance : TwoWordInstance (Fin 3) (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
  { CoreExamples.smallInstance
      ⟨0, fun q c => if q = 0 ∨ (q = 1 ∧ c = 1) then 1 else 2⟩ {2}
    with Guard := {(0, 0)} }

/-- The concrete reader stays in state one along the periodic word. -/
theorem ternaryPump_runFrom_one (k : ℕ) :
    ternaryPumpInstance.A.runFrom 1 (List.replicate k 1) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    change ternaryPumpInstance.A.runFrom (ternaryPumpInstance.A.step 1 1) _ = 1
    rw [show ternaryPumpInstance.A.step 1 1 = 1 by decide]
    exact ih

/-- The concrete reader states at each cut have this explicit form. -/
theorem ternaryPump_atCut (k s : ℕ) (hs : 1 ≤ s) :
    ternaryPumpInstance.A.atCut (2 :: List.replicate k 1) s = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hs
  change ternaryPumpInstance.A.runFrom ternaryPumpInstance.A.start
    ((2 :: List.replicate k 1).take (s + 1)) = 1
  rw [List.take_succ_cons, List.take_replicate]
  change ternaryPumpInstance.A.runFrom (ternaryPumpInstance.A.step 0 2) _ = 1
  rw [show ternaryPumpInstance.A.step 0 2 = 1 by decide]
  exact ternaryPump_runFrom_one _

/-- A nonempty guard and arbitrarily long ternary inputs to the pump. -/
theorem ternaryPump_long (k : ℕ) :
    ternaryPumpInstance.PumpGood (fun _ => 1) (2 :: List.replicate k 1) [] := by
  refine ⟨?_, ?_, by decide, ?_, ?_⟩
  · rw [TwoWordInstance.safeFrom_iff]
    intro s _
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · rw [List.take_zero]
      decide
    · change ternaryPumpInstance.A.atCut _ s ∉ _
      rw [ternaryPump_atCut k s hpos]
      decide
  · intro i hi
    simp at hi
  · refine ⟨k + 1, by simp, 0, by simp, ⟨by simp, by simp, by simp⟩, ?_⟩
    rw [Fin.fin_one_eq_zero (ternaryPumpInstance.A'.atCut _ _)]
    decide
  · intro s _ e he _ hsuf
    have he0 : e = 0 := by simpa using he
    subst he0
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h0 := congrFun hsuf 0
      simp [prepend] at h0
    · rw [ternaryPump_atCut k s hpos]
      decide

end NonMortalExamples
end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words.Mortal
open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.RejectedTail
namespace Examples

/-- A safe three-state chain followed by an unsafe sink; the target rejects on `true`, the
guard tests the start states, and the head pair is reached after the common suffix `true`. -/
def small : TwoWordInstance Bool (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  A := ⟨0, fun q _ => ⟨min (q.val+1) 3, by omega⟩⟩
  B := ⟨0, fun _ c => if c then 1 else 0⟩
  A' := ⟨0, fun _ _ => 1⟩
  B' := ⟨0, fun _ _ => 1⟩
  Bad := {3}
  Rej := {1}
  Guard := {(0,0)}
  Head := {(1,0)}

/-- `([false, true], [true])` is a mortal hole of `small`. -/
theorem mortal_01_1 : small.IsMortalHole [false,true] [true] := by decide

/-- The same chain over a ternary alphabet; the target rejects on letter `2`. -/
def ternarySmall : TwoWordInstance (Fin 3) (Fin 4) (Fin 2) (Fin 2) (Fin 2) where
  A := ⟨0, fun q _ => ⟨min (q.val+1) 3, by omega⟩⟩
  B := ⟨0, fun _ c => if c = 2 then 1 else 0⟩
  A' := ⟨0, fun _ _ => 1⟩
  B' := ⟨0, fun _ _ => 1⟩
  Bad := {3}
  Rej := {1}
  Guard := {(0,0)}
  Head := {(1,0)}

/-- `([0, 2], [2])` is a mortal hole of `ternarySmall`. -/
theorem ternary_mortal_02_2 : ternarySmall.IsMortalHole [0,2] [2] := by decide +kernel

end Examples
end DeciENSSE.Core.Words.Mortal

namespace DeciENSSE.Core.Words
namespace BoundExamples

/-- Apply the full bound to a genuine ternary ForcedHeads instance with a hole. -/
theorem ternary_bounded :
    ∃ u t, CoreExamples.ternaryBranch.IsHole u t ∧
      u.length + t.length ≤ twoWordHoleBound 2 1 1 2 :=
  shortHoleBound (Fin 3) 2 1 1 2 _
    CoreExamples.short_hypotheses.1 CoreExamples.short_hypotheses.2

/-- The empty-alphabet branch has actual ForcedHeads/hole inputs. -/
theorem empty_hypotheses :
    let I := CoreExamples.smallInstance (CoreExamples.oneDFA (α := Fin 0)) ∅
    I.ForcedHeads ∧ I.IsHole [] [] :=
  ⟨CoreExamples.smallInstance_forcedHeads _ _, by decide +kernel⟩

end BoundExamples
end DeciENSSE.Core.Words
