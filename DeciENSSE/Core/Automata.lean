import DeciENSSE.Core.Horn
import DeciENSSE.Core.Words.LDFA
import Mathlib.Data.Fintype.Powerset

/-! # Saturation and bound automata

Finite saturation computes upper and lower automata for covariant constructor
constraints, including arity zero. Their languages characterize Horn closure.

## Main declarations

- `Bound.D`
- `Bound.upper`
- `Bound.lower`
- `Bound.lowest_point`
- `Bound.liveness`
- `Bound.mu_membership`
- `Bound.cl_membership`
- `Bound.decideSat`
-/

namespace DeciENSSE.Core
namespace Bound
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Accessor searches enumerate literals, not the function space of children. -/
private theorem exists_fleArgs_iff (χ : List (Lit n V))
    (F : ((Fin n → V) × V) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.fleArgs?, F p) ↔
      ∃ a u, Lit.fle a u ∈ χ ∧ F (a, u) := by
  constructor
  · rintro ⟨l, hl, ⟨a, u⟩, hp, h⟩
    have he := (Lit.mem_fleArgs? l a u).mp hp
    subst l
    exact ⟨a, u, hl, h⟩
  · rintro ⟨a, u, hl, h⟩
    exact ⟨.fle a u, hl, (a, u), (Lit.mem_fleArgs? _ _ _).mpr rfl, h⟩

omit [Fintype V] [DecidableEq V] in
private theorem exists_lefArgs_iff (χ : List (Lit n V))
    (F : (V × (Fin n → V)) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.lefArgs?, F p) ↔
      ∃ u a, Lit.lef u a ∈ χ ∧ F (u, a) := by
  constructor
  · rintro ⟨l, hl, ⟨u, a⟩, hp, h⟩
    have he := (Lit.mem_lefArgs? l u a).mp hp
    subst l
    exact ⟨u, a, hl, h⟩
  · rintro ⟨u, a, hl, h⟩
    exact ⟨.lef u a, hl, (u, a), (Lit.mem_lefArgs? _ _ _).mpr rfl, h⟩

/-- One simultaneous round of the four rules; decomposition visits every child. -/
def round (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  R ∪ Finset.univ.filter fun p => p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
    (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
    ∃ l ∈ χ, ∃ a ∈ l.fleArgs?, ∃ k ∈ χ, ∃ b ∈ k.lefArgs?,
      ∃ i : Fin n, (a.2, b.1) ∈ R ∧ p.1 = a.1 i ∧ p.2 = b.2 i

/-- Membership in one saturation round expands into the four deduction rules. -/
@[simp] theorem mem_round {χ : List (Lit n V)} {R : Finset (V × V)} {p : V × V} :
    p ∈ round χ R ↔ p ∈ R ∨ p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
      (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
      ∃ a b u v, ∃ i : Fin n, Lit.fle a u ∈ χ ∧ (u, v) ∈ R ∧
        Lit.lef v b ∈ χ ∧ p.1 = a i ∧ p.2 = b i := by
  simp only [round, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_fleArgs_iff, exists_lefArgs_iff]
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  constructor
  · rintro ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩
    exact ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
  · rintro ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
    exact ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩

/-- Each saturation round retains all existing pairs. -/
theorem subset_round (χ : List (Lit n V)) (R : Finset (V × V)) : R ⊆ round χ R :=
  Finset.subset_union_left

/-- Saturation terminates because every recursive round adds a pair. -/
def saturate (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  if _h : round χ R ⊆ R then R else saturate χ (round χ R)
termination_by Fintype.card (V × V) - R.card
decreasing_by
  have hlt : R.card < (round χ R).card :=
    Finset.card_lt_card (ssubset_iff_subset_not_subset.mpr ⟨subset_round χ R, _h⟩)
  have hle := Finset.card_le_univ (round χ R)
  omega

/-- The finite saturated relation on variables. -/
def D (χ : List (Lit n V)) : Finset (V × V) := saturate χ ∅

/-- The saturated relation is closed under one round. -/
theorem saturate_closed (χ : List (Lit n V)) (R : Finset (V × V)) :
    round χ (saturate χ R) ⊆ saturate χ R := by
  fun_induction saturate χ R with
  | case1 R h => exact h
  | case2 R h ih => exact ih

/-- Saturation contains the initial relation. -/
theorem subset_saturate (χ : List (Lit n V)) (R : Finset (V × V)) :
    R ⊆ saturate χ R := by
  fun_induction saturate χ R with
  | case1 => exact Finset.Subset.refl _
  | case2 R _ ih => exact (subset_round χ R).trans ih

/-- The inductive presentation used to reason about the executable saturation. -/
inductive Deriv (χ : List (Lit n V)) : V → V → Prop
  | refl (x) : Deriv χ x x
  | copy {x y} : Lit.le x y ∈ χ → Deriv χ x y
  | trans {x y z} : Deriv χ x y → Deriv χ y z → Deriv χ x z
  | decomp {as bs : Fin n → V} {u v} (c : Fin n) : Lit.fle as u ∈ χ →
      Deriv χ u v → Lit.lef v bs ∈ χ →
      Deriv χ (as c) (bs c)

/-- One round preserves derivability of variable inequalities. -/
theorem round_sound {χ : List (Lit n V)} {R : Finset (V × V)}
    (hR : ∀ p ∈ R, Deriv χ p.1 p.2) : ∀ p ∈ round χ R, Deriv χ p.1 p.2 := by
  intro p hp
  rcases mem_round.mp hp with hp | hp
  · exact hR p hp
  · rcases hp with h | h | ⟨v, h₁, h₂⟩ |
      ⟨as, bs, u, v, c, hl, hd, hu, h₁, h₂⟩
    · rw [h]; exact .refl _
    · exact .copy h
    · exact .trans (hR (p.1, v) h₁) (hR (v, p.2) h₂)
    · rw [h₁, h₂]; exact .decomp c hl (hR _ hd) hu

/-- Every pair produced by saturation has an inductive derivation. -/
theorem saturate_sound (χ : List (Lit n V)) (R : Finset (V × V))
    (hR : ∀ p ∈ R, Deriv χ p.1 p.2) :
    ∀ p ∈ saturate χ R, Deriv χ p.1 p.2 := by
  fun_induction saturate χ R with
  | case1 => exact hR
  | case2 R _ ih => exact ih (round_sound hR)

/-- The saturated relation is characterized by its closure rules. -/
theorem mem_D_iff {χ : List (Lit n V)} {x y : V} : (x, y) ∈ D χ ↔ Deriv χ x y := by
  constructor
  · exact saturate_sound χ ∅ (by simp) (x, y)
  · intro h
    have hc := saturate_closed χ ∅
    induction h with
    | refl x => exact hc (by simp)
    | copy h => exact hc (by simp [h])
    | trans _ _ ih₁ ih₂ =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, ih₁, ih₂⟩)))
    | decomp c hl _ hu ih =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, c, hl, ih, hu, rfl, rfl⟩)))

/-- The saturated relation is reflexive. -/
theorem d_refl (χ : List (Lit n V)) (x : V) : (x, x) ∈ D χ := mem_D_iff.mpr (.refl x)
/-- A variable inequality is present in the saturated relation. -/
theorem d_copy {χ : List (Lit n V)} {x y : V} (h : Lit.le x y ∈ χ) :
    (x, y) ∈ D χ := mem_D_iff.mpr (.copy h)
/-- The saturated relation is transitive. -/
theorem d_trans {χ : List (Lit n V)} {x y z : V}
    (h : (x, y) ∈ D χ) (h' : (y, z) ∈ D χ) : (x, z) ∈ D χ :=
  mem_D_iff.mpr (.trans (mem_D_iff.mp h) (mem_D_iff.mp h'))
/-- Matching constructor bounds imply inequalities between corresponding children. -/
theorem d_decomp {χ : List (Lit n V)} {as bs : Fin n → V} {u v : V} (c : Fin n)
    (hl : Lit.fle as u ∈ χ) (hd : (u, v) ∈ D χ) (hu : Lit.lef v bs ∈ χ) :
    ((as c), (bs c)) ∈ D χ :=
  mem_D_iff.mpr (.decomp c hl (mem_D_iff.mp hd) hu)

/-- Leastness among all relations satisfying the rules. -/
theorem d_least {χ : List (Lit n V)} (R : V → V → Prop)
    (hr : ∀ x, R x x) (hc : ∀ x y, Lit.le x y ∈ χ → R x y)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (hd : ∀ as bs u v (c : Fin n), Lit.fle as u ∈ χ → R u v →
      Lit.lef v bs ∈ χ → R (as c) (bs c))
    {x y} (h : (x, y) ∈ D χ) : R x y := by
  have hh := mem_D_iff.mp h
  clear h
  induction hh with
  | refl x => exact hr x
  | copy h => exact hc _ _ h
  | trans _ _ h₁ h₂ => exact ht _ _ _ h₁ h₂
  | decomp c hl _ hu ih => exact hd _ _ _ _ c hl ih hu

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

/-- Move-only derivations; no facts and no truncations are included. -/
inductive Moves (χ : List (Lit n V)) (a : Config n V) : Config n V → Prop
  | refl : Moves χ a a
  | step {b c} : Moves χ a b → Move χ b c → Moves χ a c

namespace Moves
variable {χ : List (Lit n V)} {a b c : Config n V}
omit [Fintype V] [DecidableEq V] in
/-- Compose two move derivations. -/
theorem trans (h : Moves χ a b) (h' : Moves χ b c) : Moves χ a c := by
  induction h' with
  | refl => exact h
  | step _ hm ih => exact .step ih hm

omit [Fintype V] [DecidableEq V] in
/-- A move derivation is a Horn reachability derivation. -/
theorem reach (h : Moves χ a b) : Reach χ a b := by
  induction h with
  | refl => exact .refl
  | step _ hm ih => exact .step ih (.move hm)

omit [Fintype V] [DecidableEq V] in
/-- A move derivation preserves a common appended suffix. -/
theorem append (h : Moves χ a b) (σ : List (Fin n)) :
    Moves χ (a.1, a.2 ++ σ) (b.1, b.2 ++ σ) := by
  induction h with
  | refl => exact .refl
  | step _ hm ih =>
    apply Moves.step ih
    cases hm with
    | copy hl => exact .copy hl
    | push c hl => exact .push c hl
    | pop c hl => exact .pop c hl
end Moves

/-- A move derivation above σ, with σ deleted from every stack. Lifting such a derivation appends
σ back to every configuration. -/
def Above (χ : List (Lit n V)) (σ : List (Fin n)) (a b : Config n V) : Prop :=
  ∃ u v, a.2 = u ++ σ ∧ b.2 = v ++ σ ∧ Moves χ (a.1, u) (b.1, v)

omit [Fintype V] [DecidableEq V] in
/-- Remove the protected common suffix from an above-suffix derivation. -/
theorem above_iff {χ : List (Lit n V)} {a b : V} {u v σ : List (Fin n)} :
    Above χ σ (a, u ++ σ) (b, v ++ σ) ↔ Moves χ (a, u) (b, v) := by
  constructor
  · rintro ⟨u', v', hu, hv, h⟩
    have hu' : u = u' := List.append_cancel_right hu
    have hv' : v = v' := List.append_cancel_right hv
    simpa [hu', hv'] using h
  · intro h; exact ⟨u, v, rfl, rfl, h⟩

omit [Fintype V] [DecidableEq V] in
/-- A reachable stack can be truncated by any final suffix. -/
theorem reach_truncate {χ : List (Lit n V)} (y : V) (u v : List (Fin n)) :
    Reach χ (y, u ++ v) (y, u) := by
  induction v using List.reverseRecOn with
  | nil => simpa using (Reach.refl (χ := χ) (a := (y, u)))
  | append_singleton v c ih =>
    exact (Reach.step .refl (by
      simpa [List.append_assoc] using (Clause.trunc (χ := χ) y (u ++ v) c))).trans ih

omit [Fintype V] [DecidableEq V] in
/-- Replay the same moves while retaining each deleted suffix. -/
theorem truncation {χ : List (Lit n V)} {a b : Config n V} :
    Reach χ a b ↔ ∃ W, Moves χ a (b.1, W) ∧ b.2.IsPrefix W := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a.2, .refl, List.prefix_refl _⟩
    | @step b c _ hc ih =>
      obtain ⟨W, hm, v, hv⟩ := ih
      subst W
      cases hc with
      | trunc y w c =>
        exact ⟨(w ++ [c]) ++ v, hm, [c] ++ v, by simp [List.append_assoc]⟩
      | move h =>
        cases h with
        | copy hl => exact ⟨_ , .step hm (.copy hl), v, rfl⟩
        | push c hl => exact ⟨_ , .step hm (.push c hl), v, rfl⟩
        | pop c hl => exact ⟨_ , .step hm (.pop c hl), v, rfl⟩
  · rintro ⟨W, h, v, rfl⟩
    exact h.reach.trans (reach_truncate b.1 b.2 v)

/-- Balanced saturation consequences act at every unchanged suffix. -/
theorem d_moves {χ : List (Lit n V)} {a b : V} (h : (a, b) ∈ D χ) (w : List (Fin n)) :
    Moves χ (a, w) (b, w) := by
  have hh := mem_D_iff.mp h
  clear h
  induction hh generalizing w with
  | refl => exact .refl
  | copy h => exact .step .refl (.copy h)
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)
  | decomp c hl _ hu ih =>
    exact ((Moves.step .refl (.push c hl)).trans (ih (c :: w))).step (.pop c hu)

/-- Upper summaries give derivations that consume the read prefix. -/
theorem P_moves {χ : List (Lit n V)} {x b : V} {β : List (Fin n)}
    (h : b ∈ P χ x β) (σ : List (Fin n)) : Moves χ (x, β ++ σ) (b, σ) := by
  induction β using List.reverseRecOn generalizing b σ with
  | nil => exact d_moves (mem_up.mp h) σ
  | append_singleton β c ih =>
    rw [P_snoc, mem_pstep] at h
    obtain ⟨r, hr, bs, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((ih hr (c :: σ)).step (.pop c hl)).trans (d_moves hd σ)

/-- Lower summaries give derivations that produce the read prefix. -/
theorem Q_moves {χ : List (Lit n V)} {y a : V} {γ : List (Fin n)}
    (h : a ∈ Q χ y γ) (σ : List (Fin n)) : Moves χ (a, σ) (y, γ ++ σ) := by
  induction γ using List.reverseRecOn generalizing a σ with
  | nil => exact d_moves (mem_down.mp h) σ
  | append_singleton γ c ih =>
    rw [Q_snoc, mem_qstep] at h
    obtain ⟨r, hr, as, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((d_moves hd σ).step (.push c hl)).trans (ih hr (c :: σ))


/-- Changing the target along D preserves every lower summary. -/
theorem Q_target {χ : List (Lit n V)} {y z a : V} {w : List (Fin n)}
    (hyz : (y, z) ∈ D χ) (h : a ∈ Q χ y w) : a ∈ Q χ z w := by
  induction w using List.reverseRecOn generalizing a with
  | nil => exact mem_down.mpr (d_trans (mem_down.mp h) hyz)
  | append_singleton w c ih =>
    rw [Q_snoc, mem_qstep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- A push step preserves the lower-automaton summary. -/
theorem Q_push {χ : List (Lit n V)} {as : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hl : Lit.fle as y ∈ χ) (h : a ∈ Q χ (as c) w) :
    a ∈ Q χ y (c :: w) := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    exact mem_qstep.mpr ⟨y, mem_down.mpr (d_refl χ y), as, hl, mem_down.mp h⟩
  | append_singleton w d ih =>
    rw [Q_snoc, mem_qstep] at h
    change a ∈ Q χ y ((c :: w) ++ [d])
    rw [Q_snoc, mem_qstep]
    obtain ⟨r, hr, bs, hb, hd⟩ := h
    exact ⟨r, ih hr, bs, hb, hd⟩

/-- A pop step preserves the lower-automaton summary. -/
theorem Q_pop {χ : List (Lit n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : Lit.lef y bs ∈ χ) (h : a ∈ Q χ y (c :: w)) :
    a ∈ Q χ (bs c) w := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    obtain ⟨r, hr, as, hl, hd⟩ := mem_qstep.mp h
    exact mem_down.mpr (d_trans hd (d_decomp c hl (mem_down.mp hr) hu))
  | append_singleton w d ih =>
    change a ∈ Q χ y ((c :: w) ++ [d]) at h
    rw [Q_snoc, mem_qstep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- The common-suffix form of a lowest-point decomposition. -/
def Normal (χ : List (Lit n V)) (x : V) (u : List (Fin n)) (y : V) (t : List (Fin n)) : Prop :=
  ∃ β γ σ v, u = β ++ σ ∧ t = γ ++ σ ∧ v ∈ P χ x β ∧ v ∈ Q χ y γ

/-- One move preserves the normal-form summary. -/
theorem normal_step {χ : List (Lit n V)} {x y z : V} {u t w : List (Fin n)}
    (h : Normal χ x u y t) (hm : Move χ (y, t) (z, w)) : Normal χ x u z w := by
  obtain ⟨β, γ, σ, v, hu, ht, hp, hq⟩ := h
  cases hm with
  | copy hl => exact ⟨β, γ, σ, v, hu, ht, hp, Q_target (d_copy hl) hq⟩
  | push c hl =>
    exact ⟨β, c :: γ, σ, v, hu, congrArg (List.cons c) ht, hp, Q_push c hl hq⟩
  | @pop r as w c hl =>
    cases γ with
    | nil =>
      have hs : σ = c :: w := ht.symm
      refine ⟨β ++ [c], [], w, (as c), ?_, rfl, ?_, ?_⟩
      · simpa [hs, List.append_assoc] using hu
      · rw [P_snoc, mem_pstep]
        exact ⟨y, P_closed hp (mem_down.mp hq), as, hl, d_refl χ _⟩
      · exact mem_down.mpr (d_refl χ _)
    | cons d γ =>
      have he := List.cons.inj ht
      obtain ⟨rfl, hw⟩ := he
      exact ⟨β, γ, σ, v, hu, hw, hp, Q_pop c hl hq⟩

/-- Every move path has a lowest-point decomposition, proved by preserving its normal form under
copies, pushes, and pops. -/
theorem moves_normal {χ : List (Lit n V)} {a b : Config n V} (h : Moves χ a b) :
    Normal χ a.1 a.2 b.1 b.2 := by
  induction h with
  | refl => exact ⟨[], [], a.2, a.1, rfl, rfl,
      mem_up.mpr (d_refl χ _), mem_down.mpr (d_refl χ _)⟩
  | step _ hm ih => exact normal_step ih hm

/-- A normal-form summary supplies a move derivation. -/
theorem normal_moves {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal χ x u y t) : Moves χ (x, u) (y, t) := by
  obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := h
  exact (P_moves hp σ).trans (Q_moves hq σ)

/-- Saturation summarizes derivations above a protected common suffix. -/
theorem summaries_D {χ : List (Lit n V)} {a b : V} (w : List (Fin n)) :
    (a, b) ∈ D χ ↔ Above χ w (a, w) (b, w) := by
  change (a, b) ∈ D χ ↔ Above χ w (a, [] ++ w) (b, [] ++ w)
  rw [above_iff]
  constructor
  · intro h; exact d_moves h []
  · intro h
    obtain ⟨β, γ, σ, v, hβ, hγ, hp, hq⟩ := moves_normal h
    have hb : β = [] ∧ σ = [] := List.append_eq_nil_iff.mp hβ.symm
    have hg : γ = [] := (List.append_eq_nil_iff.mp hγ.symm).1
    simp only [hb.1, hg, P_nil, Q_nil, mem_up, mem_down] at hp hq
    exact d_trans hp hq

/-- Upper summaries characterize prefix-consuming derivations. -/
theorem summaries_P {χ : List (Lit n V)} {x b : V} (β σ : List (Fin n)) :
    b ∈ P χ x β ↔ Above χ σ (x, β ++ σ) (b, σ) := by
  change b ∈ P χ x β ↔ Above χ σ (x, β ++ σ) (b, [] ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using P_moves h []
  · intro h
    obtain ⟨β', γ, σ', v, he, hz, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst β'
    exact P_closed hp (mem_down.mp hq)

/-- Lower summaries characterize prefix-producing derivations. -/
theorem summaries_Q {χ : List (Lit n V)} {y a : V} (γ σ : List (Fin n)) :
    a ∈ Q χ y γ ↔ Above χ σ (a, σ) (y, γ ++ σ) := by
  change a ∈ Q χ y γ ↔ Above χ σ (a, [] ++ σ) (y, γ ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using Q_moves h []
  · intro h
    obtain ⟨β, γ', σ', v, hz, he, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst γ'
    exact Q_closed hq (mem_up.mp hp)

/-- Factor a move derivation at its lowest stack height, with two bounded cuts. -/
theorem lowest_point {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    Moves χ (x, u) (y, t) ↔ ∃ s ≤ u.length, ∃ e ≤ t.length,
      u.drop s = t.drop e ∧
      (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty := by
  constructor
  · intro h
    obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := moves_normal h
    refine ⟨β.length, by simp, γ.length, by simp, ?_, ?_⟩
    · simp
    · simpa using (show (P χ x β ∩ Q χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
  · rintro ⟨s, _, e, _, he, v, hv⟩
    apply normal_moves
    exact ⟨u.take s, t.take e, u.drop s, v, (List.take_append_drop s u).symm,
      he ▸ (List.take_append_drop e t).symm, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩


/-- A lower-root hit persists backwards along prefixes. -/
theorem Q_fact_prefix {χ : List (Lit n V)} {y : V} {u t : List (Fin n)}
    (hp : u.IsPrefix t) (h : (Q χ y t ∩ LowF χ).Nonempty) :
    (Q χ y u ∩ LowF χ).Nonempty := by
  classical
  by_cases he : u = t
  · simpa [he] using h
  · have hlt : u.length < t.length := lt_of_le_of_ne hp.length_le (by
      intro hl; exact he (hp.eq_of_length hl))
    have hn : (Q χ y t).Nonempty := h.mono Finset.inter_subset_left
    have hc := cone_prefix hn hlt
    rw [← List.prefix_iff_eq_take.mp hp] at hc
    exact Finset.not_disjoint_iff_nonempty_inter.mp hc

/-- The lower automaton recognizes the least solution, without a consistency premise. -/
theorem mu_membership {χ : List (Lit n V)} {y : V} {t : List (Fin n)} :
    (y, t) ∈ Mu χ ↔ (Q χ y t ∩ LowF χ).Nonempty := by
  constructor
  · rintro ⟨⟨r, w⟩, ⟨hw, as, hl⟩, hr⟩
    change w = [] at hw
    subst w
    obtain ⟨W, hm, hp⟩ := truncation.mp hr
    have hq : r ∈ Q χ y W := by
      apply (summaries_Q W []).mpr
      exact ⟨[], W, rfl, rfl, hm⟩
    exact Q_fact_prefix hp ⟨r, Finset.mem_inter.mpr ⟨hq, mem_LowF.mpr ⟨as, hl⟩⟩⟩
  · rintro ⟨r, hr⟩
    obtain ⟨hq, hl⟩ := Finset.mem_inter.mp hr
    obtain ⟨as, hl⟩ := mem_LowF.mp hl
    exact ⟨(r, []), ⟨rfl, as, hl⟩, by simpa using (Q_moves hq []).reach⟩

/-- Satisfiability is equivalent to absence of finite root clashes. -/
theorem satisfiable_iff (χ : List (Lit n V)) :
    (∃ ρ, Sat ρ χ) ↔ ∀ v ∈ Bot χ, Disjoint (down χ v) (LowF χ) := by
  rw [satisfiable_iff_mu_avoids]
  constructor
  · intro h v hv
    apply Finset.disjoint_left.mpr
    intro r hr hl
    exact h ((mu_membership (y := v) (t := [])).mpr 
      ⟨r, Finset.mem_inter.mpr ⟨hr, hl⟩⟩) ⟨rfl, mem_Bot.mp hv⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨r, hr⟩ := mu_membership.mp ha
    exact Finset.disjoint_left.mp (h a.1 (mem_Bot.mpr hb))
      (by simpa [hw] using (Finset.mem_inter.mp hr).1) (Finset.mem_inter.mp hr).2

/-- Executable satisfiability over arbitrary {⊥, f} trees. -/
def decideSat (χ : List (Lit n V)) : Decidable (∃ ρ, Sat ρ χ) :=
  decidable_of_iff (∀ v ∈ Bot χ, Disjoint (down χ v) (LowF χ)) (satisfiable_iff χ).symm

/-- Safety includes every cut, including the starting and final state. -/
def Safe (χ : List (Lit n V)) (x : V) (u : List (Fin n)) : Prop :=
  ∀ j ∈ Finset.range (u.length + 1), Disjoint (P χ x (u.take j)) (Bot χ)
instance {χ : List (Lit n V)} {x : V} {u : List (Fin n)} : Decidable (Safe χ x u) :=
  inferInstanceAs (Decidable (∀ j ∈ Finset.range (u.length + 1),
    Disjoint (P χ x (u.take j)) (Bot χ)))

/-- Safety means that no upper prefix meets a bottom variable. -/
theorem safe_iff (χ : List (Lit n V)) (x : V) (u : List (Fin n)) :
    Safe χ x u ↔ ∀ j ≤ u.length, Disjoint (P χ x (u.take j)) (Bot χ) := by
  simp only [Safe, Finset.mem_range, Nat.lt_succ_iff]

/-- Satisfiability excludes pushes into a bottom variable. -/
theorem liveness {χ : List (Lit n V)} (hs : ∃ ρ, Sat ρ χ) (x : V) (u : List (Fin n)) :
    (x, u) ∈ Live χ ↔ Safe χ x u := by
  rw [live_iff_reach_avoids hs, safe_iff]
  constructor
  · intro h j hj
    apply Finset.disjoint_left.mpr
    intro b hb hbot
    have hm := (P_moves hb (u.drop j)).reach
    rw [List.take_append_drop] at hm
    exact h (hm.trans (by simpa using reach_truncate (χ := χ) b [] (u.drop j)))
      ⟨rfl, mem_Bot.mp hbot⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨W, hm, _⟩ := truncation.mp ha
    obtain ⟨β, γ, σ, v, hu, _, hp, hq⟩ := moves_normal hm
    change u = β ++ σ at hu
    have hγ : γ = [] := by
      by_contra hne
      have hn : (Q χ a.1 γ).Nonempty := ⟨v, hq⟩
      have hc := cone_prefix hn (List.length_pos_iff.mpr hne)
      simp only [List.take_zero, Q_nil] at hc
      exact hc ((satisfiable_iff χ).mp hs a.1 (mem_Bot.mpr hb))
    have hp' : a.1 ∈ P χ x β := P_closed hp (by simpa [hγ] using hq)
    have hd := h β.length (by rw [hu]; simp)
    rw [hu, List.take_left] at hd
    exact Finset.disjoint_left.mp hd hp' (mem_Bot.mpr hb)

/-- Every prefix of a safe word is safe. -/
theorem safe_prefix {χ : List (Lit n V)} {x : V} {u t : List (Fin n)}
    (h : Safe χ x t) (hp : u.IsPrefix t) : Safe χ x u := by
  rw [safe_iff] at h ⊢
  intro j hj
  obtain ⟨v, rfl⟩ := hp
  simpa [List.take_append_of_le_length hj] using h j (by simp; omega)

/-- Every extension of a dead configuration is dead. -/
theorem dead_extension {χ : List (Lit n V)} (hs : ∃ ρ, Sat ρ χ) {x : V} {u : List (Fin n)}
    (h : (x, u) ∉ Live χ) (v : List (Fin n)) : (x, u ++ v) ∉ Live χ := by
  intro hl
  exact h ((liveness hs x u).mpr (safe_prefix ((liveness hs x (u ++ v)).mp hl)
    ⟨v, rfl⟩))


/-- Singleton closure is described by summaries. The prefix comparison has no ordering condition
between its two cuts. -/
theorem cl_membership {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    (y, t) ∈ Cl χ (x, u) ↔ (Q χ y t ∩ LowF χ).Nonempty ∨
      ∃ s ≤ u.length, ∃ e ≤ t.length,
        (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty ∧
        (t.drop e).IsPrefix (u.drop s) := by
  constructor
  · rintro (hm | hr)
    · exact Or.inl (mu_membership.mp hm)
    · obtain ⟨W, hm, ht⟩ := truncation.mp hr
      obtain ⟨β, γ, σ, v, hu, hW, hp, hq⟩ := moves_normal hm
      change u = β ++ σ at hu
      change W = γ ++ σ at hW
      rw [hW] at ht
      by_cases hle : γ.length ≤ t.length
      · have hg : γ.IsPrefix t := List.prefix_of_prefix_length_le (List.prefix_append γ σ) ht hle
        obtain ⟨r, hr⟩ := hg
        rw [← hr] at ht
        have hs : r.IsPrefix σ := (List.prefix_append_right_inj γ).mp ht
        right
        refine ⟨β.length, by rw [hu]; simp, γ.length, hle, ?_, ?_⟩
        · simpa [hu, ← hr] using
            (show (P χ x β ∩ Q χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
        · simpa [hu, ← hr] using hs
      · left
        have hlt : t.length < γ.length := by omega
        have htγ : t.IsPrefix γ := List.prefix_of_prefix_length_le ht
          (List.prefix_append γ σ) (by omega)
        have hc := cone_prefix (show (Q χ y γ).Nonempty from ⟨v, hq⟩) hlt
        rw [← List.prefix_iff_eq_take.mp htγ] at hc
        exact Finset.not_disjoint_iff_nonempty_inter.mp hc
  · rintro (hm | ⟨s, _, e, _, hv, hp⟩)
    · exact Or.inl (mu_membership.mpr hm)
    · obtain ⟨v, hv⟩ := hv
      obtain ⟨hpv, hqv⟩ := Finset.mem_inter.mp hv
      obtain ⟨r, hr⟩ := hp
      right
      have hm := ((P_moves hpv (u.drop s)).trans (Q_moves hqv (u.drop s))).reach
      rw [List.take_append_drop] at hm
      have he : t.take e ++ u.drop s = t ++ r := by
        rw [← hr, ← List.append_assoc, List.take_append_drop]
      rw [he] at hm
      exact hm.trans (reach_truncate y t r)

/-- A rejected final state guarantees that the first rejected cut exists. -/
theorem J_defined {χ : List (Lit n V)} {y : V} {t : List (Fin n)}
    (h : Disjoint (Q χ y t) (LowF χ)) : ∃ j, J χ y t = some j := by
  cases he : J χ y t with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have hn : ∀ i ≤ t.length, ¬ Disjoint (Q χ y (t.take i)) (LowF χ) := by
      simpa [J, List.find?_eq_none, Nat.lt_succ_iff] using he
    exact (hn t.length le_rfl (by simpa using h)).elim

/-- All cuts contributing to closure membership lie at or before J. This includes cuts at J
itself. -/
theorem cl_cuts_before_J {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)}
    {j s e : ℕ} (hj : J χ y t = some j) (he : e ≤ t.length)
    (h : (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty) : e ≤ j := by
  by_contra hle
  rw [after_J hj (by omega) he] at h
  simp at h

/-- Semantic readings of the upper and lower bound automata. -/
theorem upper_sound {χ : List (Lit n V)} {ρ : V → BFTreeN n} (hρ : Sat ρ χ)
    {x b : V} {β : List (Fin n)} (h : b ∈ P χ x β) :
    ∀ σ, β ++ σ ∈ (ρ x).K → σ ∈ (ρ b).K := by
  intro σ hs
  exact (P_moves h σ).reach.mem_of_closed ((sat_iff_sol ρ).mp hρ).closed hs

/-- A lower-automaton summary gives a valid subtree inclusion in every solution. -/
theorem lower_sound {χ : List (Lit n V)} {ρ : V → BFTreeN n} (hρ : Sat ρ χ)
    {y a : V} {γ : List (Fin n)} (h : a ∈ Q χ y γ) :
    ∀ σ, σ ∈ (ρ a).K → γ ++ σ ∈ (ρ y).K := by
  intro σ hs
  exact (Q_moves h σ).reach.mem_of_closed ((sat_iff_sol ρ).mp hρ).closed hs


/-! The trace refinement records the precise rule and letter of every move.
Truncations do not contribute a label. Thus equality of traces is stronger
than equality of the visited control variables. -/

/-- A move tagged by its literal and (for push/pop) its letter. -/
inductive TaggedMove (χ : List (Lit n V)) :
    (Lit n V × Option (Fin n)) → Config n V → Config n V → Prop
  | copy {u v w} : Lit.le u v ∈ χ → TaggedMove χ (.le u v, none) (u, w) (v, w)
  | push {a u w} (c : Fin n) : Lit.fle a u ∈ χ →
      TaggedMove χ (.fle a u, some c) ((a c), w) (u, c :: w)
  | pop {u a w} (c : Fin n) : Lit.lef u a ∈ χ →
      TaggedMove χ (.lef u a, some c) (u, c :: w) ((a c), w)

/-- `allowTrunc = false` records a move-only replay of the same trace. -/
inductive Traced (χ : List (Lit n V)) (allowTrunc : Bool) (a : Config n V) :
    List (Lit n V × Option (Fin n)) → Config n V → Prop
  | refl : Traced χ allowTrunc a [] a
  | move {labels b c label} : Traced χ allowTrunc a labels b → TaggedMove χ label b c →
      Traced χ allowTrunc a (labels ++ [label]) c
  | trunc {labels v w c} : allowTrunc = true → Traced χ allowTrunc a labels (v, w ++ [c]) →
      Traced χ allowTrunc a labels (v, w)

omit [Fintype V] [DecidableEq V] in
/-- Reachability admits a trace recording moves and truncations. -/
theorem reach_traced {χ : List (Lit n V)} {a b : Config n V} (h : Reach χ a b) :
    ∃ labels, Traced χ true a labels b := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | step _ hc ih =>
    obtain ⟨labels, h⟩ := ih
    cases hc with
    | trunc v w c => exact ⟨labels, .trunc rfl h⟩
    | move hm =>
      cases hm with
      | copy hl => exact ⟨_, .move h (.copy hl)⟩
      | push c hl => exact ⟨_, .move h (.push c hl)⟩
      | pop c hl => exact ⟨_, .move h (.pop c hl)⟩

omit [Fintype V] [DecidableEq V] in
/-- A traced derivation gives the corresponding move derivation. -/
theorem traced_moves {χ : List (Lit n V)} {a b : Config n V} {labels}
    (h : Traced χ false a labels b) : Moves χ a b := by
  induction h with
  | refl => exact .refl
  | move _ hm ih =>
    apply Moves.step ih
    cases hm with
    | copy hl => exact .copy hl
    | push c hl => exact .push c hl
    | pop c hl => exact .pop c hl
  | trunc h _ _ => cases h

omit [Fintype V] [DecidableEq V] in
/-- Replay the same literal/letter sequence with all truncations postponed. -/
theorem truncation_order {χ : List (Lit n V)} {a b : Config n V} {labels}
    (h : Traced χ true a labels b) :
    ∃ W, Traced χ false a labels (b.1, W) ∧ b.2.IsPrefix W := by
  induction h with
  | refl => exact ⟨a.2, .refl, List.prefix_refl _⟩
  | @trunc labels v₀ w c _ _ ih =>
    obtain ⟨W, hm, v, hv⟩ := ih
    subst W
    exact ⟨_, hm, [c] ++ v, by simp [List.append_assoc]⟩
  | move _ hc ih =>
    obtain ⟨W, hm, v, hv⟩ := ih
    subst W
    cases hc with
    | copy hl => exact ⟨_, .move hm (.copy hl), v, rfl⟩
    | push c hl => exact ⟨_, .move hm (.push c hl), v, rfl⟩
    | pop c hl => exact ⟨_, .move hm (.pop c hl), v, rfl⟩

/-- A derivation whose configurations all have height at least h. -/
inductive HeightMoves (χ : List (Lit n V)) (h : ℕ) (a : Config n V) : Config n V → Prop
  | refl : h ≤ a.2.length → HeightMoves χ h a a
  | step {b c} : HeightMoves χ h a b → Move χ b c → h ≤ c.2.length → HeightMoves χ h a c

omit [Fintype V] [DecidableEq V] in
/-- Appending a protected suffix gives a derivation above its length. -/
theorem moves_lift_height {χ : List (Lit n V)} {a b : Config n V}
    (h : Moves χ a b) (σ : List (Fin n)) :
    HeightMoves χ σ.length (a.1, a.2 ++ σ) (b.1, b.2 ++ σ) := by
  induction h with
  | refl => exact .refl (by simp)
  | step _ hm ih =>
    apply HeightMoves.step ih
    · cases hm with
      | copy hl => exact .copy hl
      | push c hl => exact .push c hl
      | pop c hl => exact .pop c hl
    · simp

omit [Fintype V] [DecidableEq V] in
/-- Strip a protected common suffix from one move. -/
theorem move_strip {χ : List (Lit n V)} {a b : Config n V} {η σ : List (Fin n)}
    (hm : Move χ a b) (ha : a.2 = η ++ σ) (hb : σ.length ≤ b.2.length) :
    ∃ η', b.2 = η' ++ σ ∧ Move χ (a.1, η) (b.1, η') := by
  cases hm with
  | copy hl => exact ⟨η, ha, .copy hl⟩
  | push c hl => exact ⟨c :: η, congrArg (List.cons c) ha, .push c hl⟩
  | @pop u a w c hl =>
    change c :: w = η ++ σ at ha
    cases η with
    | nil =>
      have hh := congrArg List.length ha
      simp only [List.nil_append, List.length_cons] at hh
      change σ.length ≤ w.length at hb
      omega
    | cons d η =>
      obtain ⟨rfl, hw⟩ := List.cons.inj ha
      exact ⟨η, hw, .pop c hl⟩

omit [Fintype V] [DecidableEq V] in
/-- A height-bounded path preserves and can delete its initial suffix. -/
theorem height_strip {χ : List (Lit n V)} {a b : Config n V} {σ : List (Fin n)}
    (h : HeightMoves χ σ.length a b) {η : List (Fin n)} (ha : a.2 = η ++ σ) :
    ∃ η', b.2 = η' ++ σ ∧ Moves χ (a.1, η) (b.1, η') := by
  induction h with
  | refl _ => exact ⟨η, ha, .refl⟩
  | step _ hm hb ih =>
    obtain ⟨v, hv, hm'⟩ := ih
    obtain ⟨v', hv', hs⟩ := move_strip hm hv hb
    exact ⟨v', hv', .step hm' hs⟩

omit [Fintype V] [DecidableEq V] in
/-- The protected-suffix definition is exactly the height-bounded path condition, so the summary
equivalences quantify over actual move derivations. -/
theorem above_iff_height {χ : List (Lit n V)} {a b : V} {u v σ : List (Fin n)} :
    Above χ σ (a, u ++ σ) (b, v ++ σ) ↔
      HeightMoves χ σ.length (a, u ++ σ) (b, v ++ σ) := by
  rw [above_iff]
  constructor
  · exact fun h => moves_lift_height h σ
  · intro h
    obtain ⟨v', hv, hm⟩ := height_strip h rfl
    have he : v = v' := List.append_cancel_right hv
    simpa [he] using hm

/-! Finite tables and cut identities for the suffix-sharing extraction. -/

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

omit [DecidableEq V] in
/-- The powerset state space has exponential cardinality. -/
theorem state_card : Fintype.card (Finset V) = 2 ^ Fintype.card V := Fintype.card_finset

/-- Transitions themselves always produce D-upward-closed sets. -/
theorem pstep_closed {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {a b : V}
    (ha : a ∈ pstep χ S c) (hab : (a, b) ∈ D χ) : b ∈ pstep χ S c := by
  obtain ⟨r, hr, as, hl, hd⟩ := mem_pstep.mp ha
  exact mem_pstep.mpr ⟨r, hr, as, hl, d_trans hd hab⟩

/-- Transitions themselves always produce D-downward-closed sets. -/
theorem qstep_closed {χ : List (Lit n V)} {S : Finset V} {c : Fin n} {a b : V}
    (ha : a ∈ qstep χ S c) (hba : (b, a) ∈ D χ) : b ∈ qstep χ S c := by
  obtain ⟨r, hr, as, hl, hd⟩ := mem_qstep.mp ha
  exact mem_qstep.mpr ⟨r, hr, as, hl, d_trans hba hd⟩


end Bound
end DeciENSSE.Core
