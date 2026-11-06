import DeciENSSE.Core.Automata.Saturation
import DeciENSSE.Core.Words.LDFA
import Mathlib.Data.Fintype.Powerset

/-! # Upper and lower powerset automata

The upper automaton reads prefixes consumed by pops; the lower automaton reads
prefixes produced by pushes. Both store finite sets of variables closed under
saturation: an upper state is closed upward along `D` (`P_closed`), a lower state downward
(`Q_closed`). `Core/Automata/Moves` proves their reachability interpretation, and the
variance proof (`Core.Mixed.Signed`, `Core.Mixed.Membership`) runs them on signed systems.

## Main declarations

- `Automata.upper`, `Automata.lower`, `Automata.P`, `Automata.Q`: automata and runs.
- `Automata.P_closed`, `Automata.Q_closed`: closure of the states under saturation.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Variables above a given variable in the saturated relation. -/
def up (χ : List (Lit n V)) (x : V) : Finset V := Finset.univ.filter fun y => (x, y) ∈ D χ
/-- Variables below a given variable in the saturated relation. -/
def down (χ : List (Lit n V)) (y : V) : Finset V := Finset.univ.filter fun x => (x, y) ∈ D χ
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

/-- The upper state at a cut is the state of the corresponding prefix. -/
@[simp] theorem upper_atCut (χ : List (Lit n V)) (x : V) (w : List (Fin n)) (s : ℕ) :
    (upper χ x).atCut w s = P χ x (w.take s) := rfl

/-- The lower state at a cut is the state of the corresponding prefix. -/
@[simp] theorem lower_atCut (χ : List (Lit n V)) (y : V) (w : List (Fin n)) (e : ℕ) :
    (lower χ y).atCut w e = Q χ y (w.take e) := rfl

end Automata
end DeciENSSE.Core
