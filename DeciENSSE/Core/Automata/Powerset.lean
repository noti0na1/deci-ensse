import DeciENSSE.Core.Automata.Saturation
import DeciENSSE.Core.Words.LDFA
import Mathlib.Data.Fintype.Powerset

/-! # Upper and lower powerset automata

The upper automaton reads prefixes consumed by pops; the lower automaton reads
prefixes produced by pushes. Both store finite sets of variables closed under
saturation. `cone_prefix` says that a nonempty lower run has a forced-root witness
at every strict prefix, and `after_J` says that the lower run is empty after its
first rejected cut.

This module defines the finite states and tests used by the covariant two-word
reduction. `Core/Automata/Moves` proves their reachability interpretation, and
`Core/Automata` uses it to recognize forced atoms, seed closures, and liveness.

## Main declarations

- `Automata.upper`, `Automata.lower`, `Automata.P`, `Automata.Q`: automata and runs.
- `Automata.cone_prefix`, `Automata.J`, `Automata.after_J`: forced-root cuts.
- `Automata.badStates`, `Automata.rejectedStates`, `Automata.overlapStates`:
  the finite safety, rejection, and comparison tests.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Variables above a given variable in the saturated relation. -/
def up (χ : List (Lit n V)) (x : V) : Finset V := Finset.univ.filter fun y => (x, y) ∈ D χ
/-- Variables below a given variable in the saturated relation. -/
def down (χ : List (Lit n V)) (y : V) : Finset V := Finset.univ.filter fun x => (x, y) ∈ D χ
/-- Variables constrained to bottom. -/
def Bot (χ : List (Lit n V)) : Finset V := Finset.univ.filter fun x => Lit.bot x ∈ χ
/-- Variables occurring as targets of constructor lower bounds. -/
def LowF (χ : List (Lit n V)) : Finset V :=
  Finset.univ.filter fun x => ∃ l ∈ χ, ∃ p ∈ l.fleArgs?, p.2 = x

/-- One transition of the upper powerset automaton. -/
def pstep (χ : List (Lit n V)) (P : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun b => ∃ r ∈ P, ∃ l ∈ χ, ∃ p ∈ l.lefArgs?,
    p.1 = r ∧ (p.2 c, b) ∈ D χ

/-- One transition of the lower powerset automaton. -/
def qstep (χ : List (Lit n V)) (Q : Finset V) (c : Fin n) : Finset V :=
  Finset.univ.filter fun a => ∃ r ∈ Q, ∃ l ∈ χ, ∃ p ∈ l.fleArgs?,
    p.2 = r ∧ (a, p.1 c) ∈ D χ

/-- The upper powerset automaton rooted at a variable. -/
def upper (χ : List (Lit n V)) (x : V) : LDFA (Fin n) (Finset V) := ⟨up χ x, pstep χ⟩
/-- The lower powerset automaton rooted at a variable. -/
def lower (χ : List (Lit n V)) (y : V) : LDFA (Fin n) (Finset V) := ⟨down χ y, qstep χ⟩
/-- The upper-automaton state after reading a word. -/
def P (χ : List (Lit n V)) (x : V) (w : List (Fin n)) : Finset V := (upper χ x).run w
/-- The lower-automaton state after reading a word. -/
def Q (χ : List (Lit n V)) (y : V) (w : List (Fin n)) : Finset V := (lower χ y).run w

/-- Upper-set membership agrees with the saturated relation. -/
@[simp] theorem mem_up {χ : List (Lit n V)} {x y : V} : y ∈ up χ x ↔ (x, y) ∈ D χ := by simp [up]
/-- Lower-set membership agrees with the saturated relation. -/
@[simp] theorem mem_down {χ : List (Lit n V)} {x y : V} : x ∈ down χ y ↔ (x, y) ∈ D χ := by
  simp [down]
/-- Bottom-set membership means occurrence of a bottom literal. -/
@[simp] theorem mem_Bot {χ : List (Lit n V)} {x : V} : x ∈ Bot χ ↔ Lit.bot x ∈ χ := by simp [Bot]
/-- Forced-root membership is witnessed by a constructor lower bound. -/
@[simp] theorem mem_LowF {χ : List (Lit n V)} {x : V} :
    x ∈ LowF χ ↔ ∃ a, Lit.fle a x ∈ χ := by
  simp only [LowF, Finset.mem_filter, Finset.mem_univ, true_and, exists_fleArgs_iff]
  simp
/-- An upper transition is witnessed by a constructor upper bound. -/
@[simp] theorem mem_pstep {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {b : V} :
    b ∈ pstep χ S c ↔ ∃ r ∈ S, ∃ bs, Lit.lef r bs ∈ χ ∧
      ((bs c), b) ∈ D χ := by
  simp only [pstep, Finset.mem_filter, Finset.mem_univ, true_and, exists_lefArgs_iff]
  simp [exists_and_left]
/-- A lower transition is witnessed by a constructor lower bound. -/
@[simp] theorem mem_qstep {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {a : V} :
    a ∈ qstep χ S c ↔ ∃ r ∈ S, ∃ as, Lit.fle as r ∈ χ ∧
      (a, (as c)) ∈ D χ := by
  simp only [qstep, Finset.mem_filter, Finset.mem_univ, true_and, exists_fleArgs_iff]
  constructor
  · rintro ⟨r, hr, as, u, hl, rfl, hd⟩
    exact ⟨u, hr, as, hl, hd⟩
  · rintro ⟨r, hr, as, hl, hd⟩
    exact ⟨r, hr, as, r, hl, rfl, hd⟩
/-- The initial upper state is the saturated upper set. -/
@[simp] theorem P_nil (χ : List (Lit n V)) (x : V) : P χ x [] = up χ x := rfl
/-- The initial lower state is the saturated lower set. -/
@[simp] theorem Q_nil (χ : List (Lit n V)) (x : V) : Q χ x [] = down χ x := rfl
/-- Appending a letter performs one upper transition. -/
@[simp] theorem P_snoc (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    P χ x (w ++ [c]) = pstep χ (P χ x w) c := by
  simp [P, LDFA.run, LDFA.runFrom, List.foldl_append, upper]
/-- Appending a letter performs one lower transition. -/
@[simp] theorem Q_snoc (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (c : Fin n) :
    Q χ x (w ++ [c]) = qstep χ (Q χ x w) c := by
  simp [Q, LDFA.run, LDFA.runFrom, List.foldl_append, lower]

/-- An empty upper state remains empty. -/
@[simp] theorem pstep_empty (χ : List (Lit n V)) (c : Fin n) : pstep χ ∅ c = ∅ := by ext; simp
/-- An empty lower state remains empty. -/
@[simp] theorem qstep_empty (χ : List (Lit n V)) (c : Fin n) : qstep χ ∅ c = ∅ := by ext; simp

/-- Every upper state is closed upward under saturation. -/
theorem P_closed {χ : List (Lit n V)} {x a b : V} {w : List (Fin n)}
    (ha : a ∈ P χ x w) (hab : (a, b) ∈ D χ) : b ∈ P χ x w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_up.mpr (d_trans (mem_up.mp ha) hab)
  | append_singleton w c =>
    rw [P_snoc, mem_pstep] at ha ⊢
    obtain ⟨r, hr, bs, hl, hd⟩ := ha
    exact ⟨r, hr, bs, hl, d_trans hd hab⟩

/-- Every lower state is closed downward under saturation. -/
theorem Q_closed {χ : List (Lit n V)} {y a b : V} {w : List (Fin n)}
    (ha : a ∈ Q χ y w) (hba : (b, a) ∈ D χ) : b ∈ Q χ y w := by
  cases w using List.reverseRecOn with
  | nil => exact mem_down.mpr (d_trans hba (mem_down.mp ha))
  | append_singleton w c =>
    rw [Q_snoc, mem_qstep] at ha ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := ha
    exact ⟨r, hr, as, hl, d_trans hba hd⟩

/-- A nonempty lower transition forces a constructor at the previous state. -/
theorem cone_step {χ : List (Lit n V)} {S : Finset V}
    (h : Disjoint S (LowF χ)) (c : Fin n) : qstep χ S c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨r, hr, as, hl, _⟩ := mem_qstep.mp ha
  exact Finset.disjoint_left.mp h hr (mem_LowF.mpr ⟨as, hl⟩)

/-- An empty lower state remains empty along any word. -/
theorem qrun_empty (χ : List (Lit n V)) (y : V) (w : List (Fin n)) :
    (lower χ y).runFrom ∅ w = ∅ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change (lower χ y).runFrom (qstep χ ∅ c) w = ∅
    rw [qstep_empty]; exact ih

/-- Once a lower state misses the lower roots, every strictly later state is empty. -/
theorem cone_append {χ : List (Lit n V)} {y : V} {u : List (Fin n)}
    (h : Disjoint (Q χ y u) (LowF χ)) (c : Fin n) (w : List (Fin n)) :
    Q χ y (u ++ c :: w) = ∅ := by
  rw [show u ++ c :: w = (u ++ [c]) ++ w by simp]
  change (lower χ y).runFrom (lower χ y).start ((u ++ [c]) ++ w) = ∅
  rw [LDFA.runFrom_append]
  change (lower χ y).runFrom (Q χ y (u ++ [c])) w = ∅
  rw [Q_snoc, cone_step h, qrun_empty]

/-- Every strict prefix of a nonempty lower run has a forced-root witness. -/
theorem cone_cuts {χ : List (Lit n V)} {y : V} {t : List (Fin n)} {e e' : ℕ}
    (h : Disjoint (Q χ y (t.take e)) (LowF χ)) (hee : e < e') (he' : e' ≤ t.length) :
    Q χ y (t.take e') = ∅ := by
  have hp : (t.take e).IsPrefix (t.take e') := List.take_prefix_take_left (Nat.le_of_lt hee)
  obtain ⟨v, hv⟩ := hp
  have hvn : v ≠ [] := by
    intro he
    have hl := congrArg List.length hv
    simp [he, List.length_take, Nat.min_eq_left he',
      Nat.min_eq_left (by omega : e ≤ t.length)] at hl
    omega
  cases v with
  | nil => exact (hvn rfl).elim
  | cons c v => rw [← hv]; exact cone_append h c v

/-- Once the lower run loses all forced roots, the next state is empty. -/
theorem cone_prefix {χ : List (Lit n V)} {y : V} {t : List (Fin n)}
    (h : (Q χ y t).Nonempty) {i : ℕ} (hi : i < t.length) :
    ¬ Disjoint (Q χ y (t.take i)) (LowF χ) := by
  intro hd
  have he := cone_cuts hd hi (Nat.le_refl t.length)
  simp only [List.take_length] at he
  rw [he] at h
  exact Finset.not_nonempty_empty h

/-- First lower state missing all lower roots, including cut zero. -/
def J (χ : List (Lit n V)) (y : V) (t : List (Fin n)) : Option ℕ :=
  (List.range (t.length + 1)).find? fun e =>
    decide (Disjoint (Q χ y (t.take e)) (LowF χ))

/-- The first rejected cut lies in the word and all earlier cuts are accepted. -/
theorem J_eq_some_iff (χ : List (Lit n V)) (y : V) (t : List (Fin n)) (j : ℕ) :
    J χ y t = some j ↔ Disjoint (Q χ y (t.take j)) (LowF χ) ∧ j ≤ t.length ∧
      ∀ i < j, ¬ Disjoint (Q χ y (t.take i)) (LowF χ) := by
  simp [J, List.find?_range_eq_some, Nat.lt_succ_iff]

/-- Every lower state strictly past first rejection is empty. -/
theorem after_J {χ : List (Lit n V)} {y : V} {t : List (Fin n)} {j e : ℕ}
    (hj : J χ y t = some j) (he : j < e) (hle : e ≤ t.length) :
    Q χ y (t.take e) = ∅ := cone_cuts ((J_eq_some_iff χ y t j).mp hj).1 he hle

/-! Finite tables and cut identities for the two-word extraction. -/

/-- Upper states meeting a bottom variable. -/
def badStates (χ : List (Lit n V)) : Finset (Finset V) :=
  Finset.univ.filter fun S => ¬ Disjoint S (Bot χ)

/-- Lower states with no forced-root witness. -/
def rejectedStates (χ : List (Lit n V)) : Finset (Finset V) :=
  Finset.univ.filter fun S => Disjoint S (LowF χ)

/-- Pairs of powerset states with a common variable. -/
def overlapStates (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V × Finset V) :=
  Finset.univ.filter fun p => (p.1 ∩ p.2).Nonempty

/-- Bad-state membership is intersection with the bottom variables. -/
@[simp] theorem mem_badStates {χ : List (Lit n V)} {S : Finset V} :
    S ∈ badStates χ ↔ ¬ Disjoint S (Bot χ) := by simp [badStates]

/-- Rejected-state membership is disjointness from forced roots. -/
@[simp] theorem mem_rejectedStates {χ : List (Lit n V)} {S : Finset V} :
    S ∈ rejectedStates χ ↔ Disjoint S (LowF χ) := by simp [rejectedStates]

/-- Overlap-state membership is a nonempty intersection. -/
@[simp] theorem mem_overlapStates {S T : Finset V} :
    (S, T) ∈ overlapStates V ↔ (S ∩ T).Nonempty := by simp [overlapStates]

/-- The upper state at a cut is the state of the corresponding prefix. -/
@[simp] theorem upper_atCut (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (s : ℕ) :
    (upper χ x).atCut w s = P χ x (w.take s) := rfl

/-- The lower state at a cut is the state of the corresponding prefix. -/
@[simp] theorem lower_atCut (χ : List (Lit n V)) (y : V) (w : List (Fin n)) (e : ℕ) :
    (lower χ y).atCut w e = Q χ y (w.take e) := rfl

end Automata
end DeciENSSE.Core
