import DeciENSSE.Core.Words.Self.NonMortal

/-! # Shared example instances for the word layer

Small automata and hole instances support the word, self-guarded, and mixed-signature
examples. They cover branching and mortal states, pending self events, and the empty
alphabet.

## Main declarations

- `CoreExamples.smallInstance`, `CoreExamples.ternaryBranch`, `CoreExamples.ternaryMortal`:
  two-word instances with forced target heads.
- `Self.SelfTwoWordInstanceExamples.pending`, `Self.SelfTwoWordInstanceExamples.uniqueBlocked`:
  self-guarded instances with pending or blocked holes.
- `Self.NonMortalExamples.ternaryPending`: a pending self event over a ternary alphabet.
- `Self.BoundExamples.emptyInstance`: a self-guarded instance over the empty alphabet.

The declarations retain their namespaces under `DeciENSSE.Core.Words`.
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

variable {α : Type*}

namespace CoreExamples

/-- The one-state automaton. -/
def oneDFA : LDFA α (Fin 1) := ⟨0, fun _ _ => 0⟩

/-- The automaton that leaves its start state on every letter and never returns. -/
def emptyHeadDFA : LDFA α (Fin 2) := ⟨0, fun _ _ => 1⟩

/-- `emptyHeadDFA` is in its start state only after the empty word. -/
theorem emptyHead_run_eq_zero (w : Word α) : emptyHeadDFA.run w = 0 ↔ w = [] := by
  have sink (v : Word α) : emptyHeadDFA.runFrom 1 v = 1 := by
    induction v with
    | nil => rfl
    | cons c v ih => exact ih
  cases w with
  | nil => simp [LDFA.run, LDFA.runFrom, emptyHeadDFA]
  | cons c w =>
    change emptyHeadDFA.runFrom 1 w = 0 ↔ c :: w = []
    rw [sink]
    simp

/-- A given spine automaton with immediate rejection and a head pair only at the empty
target. -/
def smallInstance {S : Type} [Fintype S] [DecidableEq S]
    (A : LDFA α S) (bad : Finset S) : TwoWordInstance α S (Fin 1) (Fin 1) (Fin 2) where
  A := A
  B := oneDFA
  A' := oneDFA
  B' := emptyHeadDFA
  Bad := bad
  Rej := {0}
  Guard := ∅
  Head := {(0, 0)}

/-- The small instances have forced target heads. -/
theorem smallInstance_forcedHeads {S : Type} [Fintype S] [DecidableEq S]
    (A : LDFA α S) (bad : Finset S) : (smallInstance A bad).ForcedHeads := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hnil := (emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hnil] at hi

/-- At state zero, letter zero is unsafe while letters one and two loop safely. -/
def ternaryBranch : TwoWordInstance (Fin 3) (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  smallInstance ⟨0, fun q c => if c = 0 then 1 else q⟩ {1}

/-- The start state of `ternaryBranch` is branching. -/
theorem ternary_branching : ternaryBranch.Branching 0 := by
  refine ⟨by decide +kernel, 0, ⟨[], by decide +kernel, rfl⟩,
    ⟨[1], by decide +kernel, by decide +kernel, rfl⟩,
    1, 2, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The empty pair is a hole of `ternaryBranch`. -/
theorem ternary_hole : ternaryBranch.IsHole [] [] := by decide +kernel

/-- The empty pair is a pre-hole of `ternaryBranch`. -/
theorem ternary_preHole : ternaryBranch.IsPreHole [] [] := by decide +kernel

/-- `ternaryBranch` has forced target heads and a hole. -/
theorem short_hypotheses : ternaryBranch.ForcedHeads ∧ ternaryBranch.HasHole :=
  ⟨smallInstance_forcedHeads _ _, [], [], ternary_hole⟩

/-- `ternaryBranch` has forced target heads and is in a non-mortal case. -/
theorem nonmortal_hypotheses : ternaryBranch.ForcedHeads ∧ ternaryBranch.NonMortalCase :=
  ⟨smallInstance_forcedHeads _ _, [], [], ternary_preHole, Or.inl ternary_branching⟩

/-- An instance whose spine start state is safe and mortal: every letter is unsafe. -/
def ternaryMortal : TwoWordInstance (Fin 3) (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  smallInstance emptyHeadDFA {1}

/-- The empty pair is a mortal hole of `ternaryMortal`. -/
theorem ternary_mortal_hole : ternaryMortal.IsMortalHole [] [] := by decide +kernel

/-- `ternaryMortal` has forced target heads and a mortal hole. -/
theorem mortal_hypotheses : ternaryMortal.ForcedHeads ∧ ternaryMortal.HasMortalHole :=
  ⟨smallInstance_forcedHeads _ _, [], [], ternary_mortal_hole⟩

/-- A unary alphabet cannot provide two distinct outgoing letters. -/
theorem unary_not_branching (I : TwoWordInstance (Fin 1) (Fin 2) (Fin 1) (Fin 1) (Fin 2))
    (q : Fin 2) : ¬ I.Branching q := by
  rintro ⟨_, r, _, _, a, b, hab, _, _⟩
  exact hab (Subsingleton.elim a b)

/-- Over an empty alphabet every safe state is mortal; no inhabitant is assumed. -/
theorem empty_mortal :
    (smallInstance (oneDFA (α := Fin 0)) ∅).Mortal 0 := by decide +kernel

end CoreExamples

end DeciENSSE.Core.Words

namespace DeciENSSE.Core.Words.Self.SelfTwoWordInstanceExamples
/-- Two states in each of the four automata; only empty heads are admitted. -/
def pending : SelfTwoWordInstance Bool (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  A := ⟨0, fun _ _ => 0⟩
  B := CoreExamples.emptyHeadDFA
  A' := CoreExamples.emptyHeadDFA
  B' := CoreExamples.emptyHeadDFA
  Bad := ∅
  Rej := {1}
  Guard := ∅
  Head := {(0, 0)}
  SelfGuard := {(0, 1)}

/-- The concrete instance satisfies the forced target heads condition. -/
theorem pending_forcedHeads : pending.ForcedHeads := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem pending_preHole : pending.IsPreHole [false] [false] := by decide +kernel
/-- The extended word pair is a self-aware hole. -/
theorem pending_completed : pending.IsHole [false, true] [false, true] := by decide +kernel

/-- The initial state has two distinct safe continuations. -/
theorem pending_branching : pending.Branching 0 := by
  refine ⟨by decide, 0, ⟨[], by decide, rfl⟩,
    ⟨[false], by decide, by decide, rfl⟩, false, true, by decide, by decide, by decide⟩

/-- Both the hole and branching-case premises of the global interfaces are inhabited. -/
theorem pending_hypotheses : pending.ForcedHeads ∧ pending.HasHole ∧ pending.NonMortalCase :=
  ⟨pending_forcedHeads, ⟨_, _, pending_completed⟩,
    ⟨_, _, pending_preHole, Or.inl pending_branching⟩⟩

/-- The target head accepts exactly [false]; its third state is the dead state. -/
def singletonHead : LDFA Bool (Fin 3) :=
  ⟨0, fun q c => if q = 0 ∧ c = false then 1 else 2⟩

/-- A unique underlying hole, with two-state A/B and a three-state target head. -/
def uniqueBlocked : SelfTwoWordInstance Bool (Fin 2) (Fin 2) (Fin 2) (Fin 3) where
  A := CoreExamples.emptyHeadDFA
  B := CoreExamples.emptyHeadDFA
  A' := ⟨0, fun _ _ => 0⟩
  B' := singletonHead
  Bad := {1}
  Rej := {1}
  Guard := ∅
  Head := {(0, 1)}
  SelfGuard := {(0, 1)}

end DeciENSSE.Core.Words.Self.SelfTwoWordInstanceExamples

namespace DeciENSSE.Core.Words.Self

namespace NonMortalExamples
/-- A ternary pending self event: zero is unsafe, while one and two are safe. -/
def ternaryPending : SelfTwoWordInstance (Fin 3) (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  A := CoreExamples.ternaryBranch.A
  B := CoreExamples.emptyHeadDFA
  A' := CoreExamples.emptyHeadDFA
  B' := CoreExamples.emptyHeadDFA
  Bad := {1}
  Rej := {1}
  Guard := ∅
  Head := {(0, 0)}
  SelfGuard := {(0, 1)}

/-- The concrete instance satisfies the forced target heads condition. -/
theorem ternaryPending_forcedHeads : ternaryPending.ForcedHeads := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hn := (CoreExamples.emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hn] at hi

/-- A concrete safe departure breaks the pending ternary self event. -/
theorem ternary_pending_completion : ternaryPending.IsHole [1, 2] [1, 2] := by
  apply ternaryPending.preHole_complete (u := [1]) (t := [1])
    (by decide +kernel) (θ := [2])
  · refine ⟨by decide +kernel, ?_⟩
    intro s e he
    exact (Finset.notMem_empty _ he.2.2).elim
  · decide +kernel

end NonMortalExamples

namespace BoundExamples
/-- Self guards may be nonempty even when the alphabet is empty. -/
def emptyInstance : SelfTwoWordInstance (Fin 0) (Fin 1) (Fin 1) (Fin 1) (Fin 2) where
  toTwoWordInstance := CoreExamples.smallInstance CoreExamples.oneDFA ∅
  SelfGuard := {(0, 0)}

end BoundExamples

end DeciENSSE.Core.Words.Self
