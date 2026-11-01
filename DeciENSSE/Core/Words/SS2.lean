import DeciENSSE.Core.Words.LDFA
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic

/-! # Two-word hole instances

An instance consists of a spine automaton `A` with unsafe states `Bad`, a target
automaton `B` with rejected states `Rej`, two head automata `A'` and `B'`, a guard on
pairs of spine and target states, and a head relation on pairs of head states. A hole is
a pair of words `(u, t)`: the spine `u` is safe, the target `t` has a rejected cut, no
cross comparison up to the first rejected cut is guarded, and some aligned comparison
carries a head pair. This module also defines the kinds of spine states used to split the
hole problem: mortal, branching and thin states.

Mortality is decided by enumerating finite sets of safe states in which every state has a
safe successor; `mortal_iff` identifies this test with the absence of an infinite safe
word.

## Main declarations

- `SS2`: two-word hole instances.
- `SS2.J`, `SS2.Event`, `SS2.HeadEvent`, `SS2.IsHole`: the first rejected cut, events,
  head events and holes.
- `SS2.FH`: forced target heads.
- `SS2.IsPreHole`: pre-holes, whose target ends at its first rejected cut.
- `SS2.Viable`, `SS2.viable_iff`, `SS2.Mortal`, `SS2.mortal_iff`: infinite safe
  continuations and mortal states.
- `SS2.Branching`, `SS2.Thin`, `SS2.IsMortalHole`, `SS2.NonMortalCase`: kinds of states,
  mortal holes, and the non-mortal cases.
- `CoreExamples`: small instances with holes of each kind.

The declarations are in the namespace `DeciENSSE.Core`.
-/

namespace DeciENSSE.Core

variable {α : Type*}

/-- A two-word hole instance over the alphabet `α`. -/
structure SS2 (α SA SB SA' SB' : Type*) [Fintype SA] [Fintype SB]
    [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
    [DecidableEq SA'] [DecidableEq SB'] where
  /-- The spine automaton. -/
  A : LDFA α SA
  /-- The target automaton. -/
  B : LDFA α SB
  /-- The head automaton of the spine. -/
  A' : LDFA α SA'
  /-- The head automaton of the target. -/
  B' : LDFA α SB'
  /-- The unsafe spine states. -/
  Bad : Finset SA
  /-- The rejected target states. -/
  Rej : Finset SB
  /-- The guarded pairs of spine and target states. -/
  Guard : Finset (SA × SB)
  /-- The head relation. -/
  Head : Finset (SA' × SB')

namespace SS2
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-- Reading `w` from `q`, the spine automaton visits only safe states, including both
endpoints. -/
def SafeFrom (q : SA) (w : Word α) : Prop :=
  ∀ s ∈ Finset.range (w.length + 1), I.A.runFrom q (w.take s) ∉ I.Bad

/-- Safety of a path is decidable. -/
instance instDecidableSafeFrom (q : SA) (w : Word α) : Decidable (I.SafeFrom q w) :=
  inferInstanceAs (Decidable (∀ s ∈ Finset.range (w.length + 1),
    I.A.runFrom q (w.take s) ∉ I.Bad))

/-- The first rejected cut of the target, found by an ascending search that includes the
cuts zero and `t.length`. -/
def J (t : Word α) : Option ℕ :=
  (List.range (t.length + 1)).find? (fun e => decide (I.B.atCut t e ∈ I.Rej))

/-- `J t = some j` iff `j` is the least rejected cut of `t`. -/
theorem J_eq_some_iff (t : Word α) (j : ℕ) :
    I.J t = some j ↔ I.B.atCut t j ∈ I.Rej ∧ j ≤ t.length ∧
      ∀ i < j, I.B.atCut t i ∉ I.Rej := by
  simp [J, List.find?_range_eq_some, Nat.lt_add_one_iff]

/-- `J t = none` iff no cut of `t` is rejected. -/
theorem J_eq_none_iff (t : Word α) :
    I.J t = none ↔ ∀ i ≤ t.length, I.B.atCut t i ∉ I.Rej := by
  simp [J, List.find?_eq_none, Nat.lt_add_one_iff]

/-- A cross comparison: the suffix of the target at `e` is a prefix of the suffix of the
spine at `s`. -/
def Cross (u t : Word α) (s e : ℕ) : Prop :=
  s ≤ u.length ∧ e ≤ t.length ∧ (t.drop e).IsPrefix (u.drop s)

/-- An aligned comparison: the suffixes of the spine at `s` and of the target at `e`
coincide. -/
def Aligned (u t : Word α) (s e : ℕ) : Prop :=
  s ≤ u.length ∧ e ≤ t.length ∧ u.drop s = t.drop e

/-- An event: a guarded cross comparison that ends at or before the first rejected cut. -/
def Event (u t : Word α) (s e : ℕ) : Prop :=
  Cross u t s e ∧ (∃ j ∈ I.J t, e ≤ j) ∧
    (I.A.atCut u s, I.B.atCut t e) ∈ I.Guard

/-- A head event: an aligned comparison whose head states form a head pair. -/
def HeadEvent (u t : Word α) (s e : ℕ) : Prop :=
  Aligned u t s e ∧ (I.A'.atCut u s, I.B'.atCut t e) ∈ I.Head

/-- The pair has a head event. -/
def HasHeadEvent (u t : Word α) : Prop :=
  ∃ s ∈ Finset.range (u.length + 1), ∃ e ∈ Finset.range (t.length + 1),
    I.HeadEvent u t s e

/-- A hole: a safe spine, a target with a rejected cut, no event, and a head event. All cut
ranges are inclusive. -/
def IsHole (u t : Word α) : Prop :=
  I.SafeFrom I.A.start u ∧ (I.J t).isSome = true ∧
  (∀ s ∈ Finset.range (u.length + 1), ∀ e ∈ Finset.range (t.length + 1),
    ¬ I.Event u t s e) ∧ I.HasHeadEvent u t

/-- Holes are decidable. -/
instance instDecidableIsHole [DecidableEq α] (u t : Word α) : Decidable (I.IsHole u t) := by
  unfold IsHole HasHeadEvent HeadEvent Event Cross Aligned
  infer_instance

/-- The instance has a hole. -/
def HasHole : Prop := ∃ u t, I.IsHole u t

/-- Forced target heads: for a head pair whose spine head is reachable, no word that leads
the target head automaton to its target head has a rejected proper prefix. -/
def FH : Prop := ∀ p q, (p, q) ∈ I.Head → I.A'.Reachable p →
  ∀ γ, I.B'.run γ = q → ∀ i, i < γ.length → I.B.atCut γ i ∉ I.Rej

/-- A pre-hole: a safe spine, a target whose first rejected cut is its end, a head event,
and no event at an aligned comparison. -/
def IsPreHole (u t : Word α) : Prop :=
  I.SafeFrom I.A.start u ∧ I.J t = some t.length ∧ I.HasHeadEvent u t ∧
    ∀ s ∈ Finset.range (u.length + 1), ∀ e ∈ Finset.range (t.length + 1),
      ¬ (I.Event u t s e ∧ Aligned u t s e)

/-- Pre-holes are decidable. -/
instance instDecidableIsPreHole [DecidableEq α] (u t : Word α) :
    Decidable (I.IsPreHole u t) := by
  unfold IsPreHole HasHeadEvent HeadEvent Event Cross Aligned
  infer_instance

/-- Reachability in the safe graph of the spine, including paths of length zero. -/
def SafeReachable (q r : SA) : Prop :=
  ∃ w, I.SafeFrom q w ∧ I.A.runFrom q w = r

/-- `q` lies on a nonempty safe cycle. -/
def Cyclic (q : SA) : Prop :=
  ∃ w, w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q

/-- An infinite word is safe from `q` when every state on its run is safe. -/
def InfiniteSafe (q : SA) (ξ : ℕ → α) : Prop :=
  ∀ n, I.A.streamRun q ξ n ∉ I.Bad

/-- A finite certificate for an infinite safe continuation: a set of safe states that
contains `q` and gives each of its states a successor in the set. -/
def Viable (q : SA) : Prop := ∃ T : Finset SA, q ∈ T ∧
  ∀ r ∈ T, r ∉ I.Bad ∧ ∃ c : α, I.A.step r c ∈ T

/-- Viability is decidable over a finite alphabet. -/
instance instDecidableViable [Fintype α] (q : SA) : Decidable (I.Viable q) := by
  unfold Viable; infer_instance

/-- A state is viable iff some infinite word is safe from it. -/
theorem viable_iff (q : SA) : I.Viable q ↔ ∃ ξ, I.InfiniteSafe q ξ := by
  classical
  constructor
  · rintro ⟨T, hq, hT⟩
    let next (r : {r // r ∈ T}) : α := (hT r r.property).2.choose
    have hn (r : {r // r ∈ T}) : I.A.step r (next r) ∈ T :=
      (hT r r.property).2.choose_spec
    let path : ℕ → {r // r ∈ T} := fun n =>
      Nat.rec ⟨q, hq⟩ (fun _ r => ⟨I.A.step r (next r), hn r⟩) n
    let ξ : ℕ → α := fun n => next (path n)
    have hp (n) : I.A.streamRun q ξ n = (path n).val := by
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg (fun r => I.A.step r (ξ n)) ih
    refine ⟨ξ, fun n => ?_⟩
    rw [hp]
    exact (hT _ (path n).property).1
  · rintro ⟨ξ, hξ⟩
    let T := (Set.range (I.A.streamRun q ξ)).toFinite.toFinset
    have memT (r) : r ∈ T ↔ ∃ n, I.A.streamRun q ξ n = r := by simp [T]
    refine ⟨T, (memT q).2 ⟨0, rfl⟩, ?_⟩
    intro r hr
    obtain ⟨n, rfl⟩ := (memT r).1 hr
    exact ⟨hξ n, ξ n, (memT _).2 ⟨n + 1, rfl⟩⟩

/-- Mortal states are safe states with no infinite safe continuation. Unsafe states are not
mortal. -/
def Mortal (q : SA) : Prop := q ∉ I.Bad ∧ ¬ I.Viable q

/-- Mortality is decidable over a finite alphabet. -/
instance instDecidableMortal [Fintype α] (q : SA) : Decidable (I.Mortal q) := by
  unfold Mortal; infer_instance

/-- A state is mortal iff it is safe and no infinite word is safe from it. -/
theorem mortal_iff (q : SA) :
    I.Mortal q ↔ q ∉ I.Bad ∧ ¬ ∃ ξ, I.InfiniteSafe q ξ := by
  rw [Mortal, viable_iff]

/-- A safe state that safely reaches a safe cycle with two distinct safe outgoing letters. -/
def Branching (q : SA) : Prop := q ∉ I.Bad ∧
  ∃ r, I.SafeReachable q r ∧ I.Cyclic r ∧
    ∃ a b : α, a ≠ b ∧ I.A.step r a ∉ I.Bad ∧ I.A.step r b ∉ I.Bad

/-- A safe state that is neither mortal nor branching. -/
def Thin (q : SA) : Prop := q ∉ I.Bad ∧ ¬ I.Mortal q ∧ ¬ I.Branching q

/-- A mortal hole: a hole whose spine ends in a mortal state and whose target ends fewer than
`|SA|` letters after its first rejected cut. -/
def IsMortalHole (u t : Word α) : Prop :=
  I.IsHole u t ∧ I.Mortal (I.A.run u) ∧
    ∃ j ∈ I.J t, t.length - j < Fintype.card SA

/-- Mortal holes are decidable over a finite alphabet. -/
instance instDecidableIsMortalHole [Fintype α] [DecidableEq α] (u t : Word α) :
    Decidable (I.IsMortalHole u t) := by
  unfold IsMortalHole; infer_instance

/-- The instance has a mortal hole. -/
def HasMortalHole : Prop := ∃ u t, I.IsMortalHole u t

/-- The cross comparison `(s, e)` survives every finite extension of both words by the same
prefix of `ξ`. -/
def Survives (u t : Word α) (s e : ℕ) (ξ : ℕ → α) : Prop :=
  ∀ n, ((t ++ streamPrefix ξ n).drop e).IsPrefix
    ((u ++ streamPrefix ξ n).drop s)

/-- No event of `(u, t)` survives the extension by `ξ`. -/
def SurvivorFree (u t : Word α) (ξ : ℕ → α) : Prop :=
  ∀ s e, I.Event u t s e → ¬ Survives u t s e ξ

/-- The two non-mortal cases: a pre-hole whose spine ends in a branching state, or in a thin
state with an infinite safe continuation that no event survives. -/
def NonMortalCase : Prop := ∃ u t, I.IsPreHole u t ∧
  (I.Branching (I.A.run u) ∨ (I.Thin (I.A.run u) ∧
    ∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ))

end SS2

/-! ## Small instances -/

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
    (A : LDFA α S) (bad : Finset S) : SS2 α S (Fin 1) (Fin 1) (Fin 2) where
  A := A
  B := oneDFA
  A' := oneDFA
  B' := emptyHeadDFA
  Bad := bad
  Rej := {0}
  Guard := ∅
  Head := {(0, 0)}

/-- The small instances have forced target heads. -/
theorem smallInstance_fh {S : Type} [Fintype S] [DecidableEq S]
    (A : LDFA α S) (bad : Finset S) : (smallInstance A bad).FH := by
  intro p q hp _ γ hγ i hi
  have hq : q = 0 := (Prod.mk.inj (Finset.mem_singleton.mp hp)).2
  have hnil := (emptyHead_run_eq_zero γ).mp (hγ.trans hq)
  simp [hnil] at hi

/-- At state zero, letter zero is unsafe while letters one and two loop safely. -/
def ternaryBranch : SS2 (Fin 3) (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
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
theorem short_hypotheses : ternaryBranch.FH ∧ ternaryBranch.HasHole :=
  ⟨smallInstance_fh _ _, [], [], ternary_hole⟩

/-- `ternaryBranch` has forced target heads and is in a non-mortal case. -/
theorem nonmortal_hypotheses : ternaryBranch.FH ∧ ternaryBranch.NonMortalCase :=
  ⟨smallInstance_fh _ _, [], [], ternary_preHole, Or.inl ternary_branching⟩

/-- An instance whose spine start state is safe and mortal: every letter is unsafe. -/
def ternaryMortal : SS2 (Fin 3) (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  smallInstance emptyHeadDFA {1}

/-- The empty pair is a mortal hole of `ternaryMortal`. -/
theorem ternary_mortal_hole : ternaryMortal.IsMortalHole [] [] := by decide +kernel

/-- `ternaryMortal` has forced target heads and a mortal hole. -/
theorem mortal_hypotheses : ternaryMortal.FH ∧ ternaryMortal.HasMortalHole :=
  ⟨smallInstance_fh _ _, [], [], ternary_mortal_hole⟩

/-- A unary alphabet cannot provide two distinct outgoing letters. -/
theorem unary_not_branching (I : SS2 (Fin 1) (Fin 2) (Fin 1) (Fin 1) (Fin 2))
    (q : Fin 2) : ¬ I.Branching q := by
  rintro ⟨_, r, _, _, a, b, hab, _, _⟩
  exact hab (Subsingleton.elim a b)

/-- Over an empty alphabet every safe state is mortal; no inhabitant is assumed. -/
theorem empty_mortal :
    (smallInstance (oneDFA (α := Fin 0)) ∅).Mortal 0 := by decide +kernel

end CoreExamples

end DeciENSSE.Core
