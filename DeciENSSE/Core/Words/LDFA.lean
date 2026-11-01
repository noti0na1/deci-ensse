import Mathlib.Computability.DFA
import Mathlib.Data.Finset.Image
import DeciNSSE.RejectedTail.Forced

/-! # Deterministic word automata over arbitrary alphabets

`LDFA` stands for labeled deterministic finite automaton. Unlike Mathlib’s `DFA`, it
has no accepting-state set: acceptance is supplied separately for each word instance.
A complete deterministic automaton without accepting states reads finite words, and the
prefixes of infinite words, over an arbitrary alphabet. Its states can be renamed along an
equivalence, two automata run in parallel as a product, and a safe path can be shortened
below the number of states without changing its endpoint. Over a finite alphabet the words
of bounded length are enumerated executably; the empty alphabet needs no special case.

## Main declarations

- `Word`, `LDFA`: words and complete deterministic automata.
- `LDFA.runFrom`, `LDFA.run`, `LDFA.atCut`, `LDFA.streamRun`: runs on words, at cuts, and
  on infinite words.
- `LDFA.streamRun_eq`: runs on finite prefixes from `DeciNSSE.RejectedTail.streamPrefix`.
- `LDFA.rename`: renaming the states along an equivalence.
- `LDFA.PathSafe`, `LDFA.short_safe_path`: paths that stay in a set of states, and short
  safe paths with the same endpoint.
- `LDFA.prod`: products of automata.
- `wordsUpTo`, `mem_wordsUpTo`: the words of length at most `n`.

The declarations are in the namespace `DeciENSSE.Core.Words`.
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

/-- Words over the alphabet `α`. -/
abbrev Word (α : Type*) := List α

/-- A complete deterministic automaton, without accepting states. -/
structure LDFA (α S : Type*) where
  /-- The start state. -/
  start : S
  /-- The transition function. -/
  step : S → α → S

variable {α : Type*}

namespace LDFA
variable {S : Type*}

/-- The state reached from `q` after reading `w`. -/
def runFrom (M : LDFA α S) (q : S) (w : Word α) : S := w.foldl M.step q

/-- The state reached from the start state after reading `w`. -/
def run (M : LDFA α S) (w : Word α) : S := M.runFrom M.start w

/-- The state at cut `s` of `w`, that is, after its first `s` letters. -/
def atCut (M : LDFA α S) (w : Word α) (s : ℕ) : S := M.run (w.take s)

/-- A state is reachable when some word leads to it from the start state. -/
def Reachable (M : LDFA α S) (q : S) : Prop := ∃ w, M.run w = q

/-- Reading the empty word stays in place. -/
@[simp] theorem runFrom_nil (M : LDFA α S) (q : S) : M.runFrom q [] = q := rfl

/-- Runs compose along concatenation. -/
@[simp] theorem runFrom_append (M : LDFA α S) (q : S) (u v : Word α) :
    M.runFrom q (u ++ v) = M.runFrom (M.runFrom q u) v := List.foldl_append

/-- The state after `n` letters of an infinite word. -/
def streamRun (M : LDFA α S) (q : S) (ξ : ℕ → α) : ℕ → S
  | 0 => q
  | n + 1 => M.step (M.streamRun q ξ n) (ξ n)

end LDFA

/-- The run on an infinite word is the run on its finite prefixes. -/
theorem LDFA.streamRun_eq {S : Type*} (M : LDFA α S) (q : S) (ξ : ℕ → α) (n : ℕ) :
    M.streamRun q ξ n = M.runFrom q (streamPrefix ξ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [streamPrefix_succ, LDFA.streamRun, ih,
      LDFA.runFrom, List.foldl_append]

namespace LDFA
variable {S T : Type*}

/-- Rename the states of an automaton along an equivalence. -/
def rename (M : LDFA α S) (e : S ≃ T) : LDFA α T where
  start := e M.start
  step q c := e (M.step (e.symm q) c)

/-- Runs of a renamed automaton are renamed runs. -/
@[simp] theorem rename_runFrom (M : LDFA α S) (e : S ≃ T) (q : S) (w : Word α) :
    (M.rename e).runFrom (e q) w = e (M.runFrom q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih => simpa [runFrom, rename] using ih (M.step q c)

/-- Runs from the start state of a renamed automaton are renamed runs. -/
@[simp] theorem rename_run (M : LDFA α S) (e : S ≃ T) (w : Word α) :
    (M.rename e).run w = e (M.run w) := rename_runFrom M e M.start w

/-- States at cuts of a renamed automaton are renamed states. -/
@[simp] theorem rename_atCut (M : LDFA α S) (e : S ≃ T) (w : Word α) (s : ℕ) :
    (M.rename e).atCut w s = e (M.atCut w s) := rename_run M e (w.take s)

/-- Renaming preserves reachability. -/
@[simp] theorem rename_reachable (M : LDFA α S) (e : S ≃ T) (q : S) :
    (M.rename e).Reachable (e q) ↔ M.Reachable q := by simp [Reachable]

/-- Runs of a renamed automaton on infinite words are renamed runs. -/
@[simp] theorem rename_streamRun (M : LDFA α S) (e : S ≃ T)
    (q : S) (ξ : ℕ → α) (n : ℕ) :
    (M.rename e).streamRun (e q) ξ n = e (M.streamRun q ξ n) := by
  simp only [streamRun_eq, rename_runFrom]
end LDFA

namespace LDFA
variable {S : Type*}

/-- Every state visited by a run, including both endpoints, satisfies `G`. -/
def PathSafe (M : LDFA α S) (G : S → Prop) (q : S) : Word α → Prop
  | [] => G q
  | c :: w => G q ∧ M.PathSafe G (M.step q c) w

/-- A path is safe iff the state at each of its cuts satisfies `G`. -/
theorem pathSafe_iff (M : LDFA α S) (G : S → Prop) (q : S) (w : Word α) :
    M.PathSafe G q w ↔ ∀ j ≤ w.length, G (M.runFrom q (w.take j)) := by
  induction w generalizing q with
  | nil => simp [PathSafe, runFrom]
  | cons c w ih =>
    rw [PathSafe, ih]
    constructor
    · rintro ⟨hq, hw⟩ j hj
      cases j with
      | zero => exact hq
      | succ j => exact hw j (by simpa using hj)
    · intro h
      exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by simp; omega)⟩

/-- Safety of a concatenation splits at the junction. -/
theorem pathSafe_append (M : LDFA α S) (G : S → Prop) (q : S) (u v : Word α) :
    M.PathSafe G q (u ++ v) ↔
      M.PathSafe G q u ∧ M.PathSafe G (M.runFrom q u) v := by
  induction u generalizing q with
  | nil =>
    change M.PathSafe G q v ↔ G q ∧ M.PathSafe G q v
    exact ⟨fun h => ⟨(pathSafe_iff M G q v).mp h 0 (by omega), h⟩, And.right⟩
  | cons c u ih =>
    change (G q ∧ M.PathSafe G (M.step q c) (u ++ v)) ↔
      (G q ∧ M.PathSafe G (M.step q c) u) ∧ M.PathSafe G (M.runFrom (M.step q c) u) v
    rw [ih, and_assoc]

/-- Loop deletion: a safe path has a safe path to the same endpoint that is shorter than
the number of states. -/
theorem short_safe_path [Fintype S] (M : LDFA α S) (G : S → Prop) (q : S)
    (w : Word α) (h : M.PathSafe G q w) :
    ∃ v, v.length < Fintype.card S ∧ M.PathSafe G q v ∧ M.runFrom q v = M.runFrom q w := by
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : w.length < Fintype.card S
    · exact ⟨w, hn, h, rfl⟩
    · let A : DFA α S := ⟨M.step, q, Set.univ⟩
      obtain ⟨r, a, b, c, he, _, hb, ha, hloop, hc⟩ :=
        A.evalFrom_split (s := q) (x := w) (t := M.runFrom q w) (by omega) rfl
      change M.runFrom q a = r at ha
      change M.runFrom r b = r at hloop
      change M.runFrom r c = M.runFrom q w at hc
      have hs := h
      rw [he, pathSafe_append, pathSafe_append] at hs
      have hs' : M.PathSafe G q (a ++ c) := by
        apply (pathSafe_append M G q a c).mpr
        refine ⟨hs.1.1, ?_⟩
        have heq : M.runFrom q (a ++ b) = M.runFrom q a := by
          rw [runFrom_append, ha, hloop]
        simpa [heq] using hs.2
      have hlen : (a ++ c).length < n := by
        have hbpos := List.length_pos_iff.mpr hb
        simp only [he, List.length_append] at hw
        simp only [List.length_append]
        omega
      obtain ⟨v, hv, hvs, hve⟩ := ih _ hlen (a ++ c) hs' rfl
      exact ⟨v, hv, hvs, hve.trans (by rw [runFrom_append, ha, hc])⟩

/-- The product of two complete automata. -/
def prod {T : Type*} (M : LDFA α S) (N : LDFA α T) : LDFA α (S × T) :=
  ⟨(M.start, N.start), fun q c => (M.step q.1 c, N.step q.2 c)⟩

/-- The product runs both automata in parallel. -/
theorem prod_runFrom {T : Type*} (M : LDFA α S) (N : LDFA α T)
    (p : S) (q : T) (w : Word α) :
    (M.prod N).runFrom (p, q) w = (M.runFrom p w, N.runFrom q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons c w ih => exact ih _ _

/-- The product runs both automata in parallel from their start states. -/
@[simp] theorem prod_run {T : Type*} (M : LDFA α S) (N : LDFA α T) (w : Word α) :
    (M.prod N).run w = (M.run w, N.run w) := prod_runFrom M N M.start N.start w

end LDFA

/-- The words of length at most `n`, also for an empty alphabet. -/
def wordsUpTo [Fintype α] [DecidableEq α] : ℕ → Finset (Word α)
  | 0 => {[]}
  | n + 1 => insert [] (Finset.univ.biUnion fun a : α =>
      (wordsUpTo n).image (List.cons a))

/-- `wordsUpTo n` consists exactly of the words of length at most `n`. -/
@[simp] theorem mem_wordsUpTo [Fintype α] [DecidableEq α] (w : Word α) (n : ℕ) :
    w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons c w => simp [wordsUpTo, ih]

end DeciENSSE.Core.Words
