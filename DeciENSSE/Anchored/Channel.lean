import DeciNSSE.Holes.Hierarchy.Reader

/-! # Positive channels and anchored comparisons

A positive channel on a lettered monitor adds an existential condition to holes: a
positive hole is a hole that also has a witness of one of four kinds, read from labels and
from one letter. The final label may satisfy `F`; a nonterminal comparison may have its
labels in `R` and its continuation letter in `Φ`; a cut may be in `S` with the final label;
or a cut may be in `S'` with the final label while its own letter is in `Φ`. The
continuation letter of a comparison `(x, y)` of `v` is the letter at `x + |v| - y`, right
after the matched factor.

For a reader, the base channel tests a relation `Pi` on reader states and takes `Φ` to be
the separator. On a word with exactly one separator, its positive condition is the
existence of an anchored comparison in `Pi`: a comparison whose matched factor ends right
before the separator.

## Main declarations

- `PosChan`, `withPos`: positive channels, and the monitor carrying `F`, `R` and `S` as its
  target and admissions.
- `At`, `Pos`, `PosHole`: letter tests at a cut, the positive condition and positive holes.
- `pos_iff_bounded`, `decPos`: the positive condition over bounded cuts, and its decision.
- `baseChan`, `pos_base_iff_comparison`: the base channel of a reader.
- `AnchoredAt`, `pos_base_iff_anchored`: with one separator, the base channel is an
  anchored comparison.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.Holes
open scoped List

/-- A positive channel: a final test `F`, three label relations `R`, `S`, `S'`, and a
letter test `Φ`. -/
structure PosChan (Γ C : Type*) where
  /-- The test of the final core and letter. -/
  F : C → Γ → Prop
  /-- The relation at nonterminal comparisons, with a continuation-letter test. -/
  R : Lab Γ C → Lab Γ C → Prop
  /-- The relation of a cut with the final label. -/
  S : Lab Γ C → Lab Γ C → Prop
  /-- The relation of a cut with the final label, with a letter test at the cut. -/
  S' : Lab Γ C → Lab Γ C → Prop
  /-- The letter test. -/
  Φ : Γ → Prop

variable {Γ C : Type*}

/-- The monitor `D` with `F` as target and `R`, `S` as interior and terminal admissions. -/
def withPos (D : Lettered Γ C) (P : PosChan Γ C) : Lettered Γ C :=
  { D with Λ := P.R, Λf := P.S, Tf := P.F }

/-- The shifted labels do not depend on the admissions. -/
@[simp] theorem zlab_withPos (D : Lettered Γ C) (P : PosChan Γ C) :
    zlab (withPos D P) = zlab D := rfl

/-- The exit cores do not depend on the admissions. -/
@[simp] theorem fcore_withPos (D : Lettered Γ C) (P : PosChan Γ C) :
    fcore (withPos D P) = fcore D := rfl

/-- The labels do not depend on the admissions. -/
@[simp] theorem label_withPos (D : Lettered Γ C) (P : PosChan Γ C) :
    (withPos D P).label = D.label := rfl

/-- A letter test at a cut, false outside the word. -/
def At (Φ : Γ → Prop) (w : List Γ) (i : ℕ) : Prop :=
  ∃ a, w[i]? = some a ∧ Φ a

/-- Letter tests are decidable. -/
instance decAt (Φ : Γ → Prop) [DecidablePred Φ] (w : List Γ) (i : ℕ) :
    Decidable (At Φ w i) := by
  unfold At
  cases h : w[i]? with
  | none => exact isFalse (by simp)
  | some a => exact decidable_of_iff (Φ a) (by simp)

/-- The positive condition: one of the clauses `F`, `R`, `S` and `S'`. -/
def Pos (D : Lettered Γ C) (P : PosChan Γ C) (v : List Γ) : Prop :=
  (∃ c a, D.label v v.length = some (c, a) ∧ P.F c a) ∨
  (∃ x y, IsComp v x y ∧ y < v.length ∧ P.R (D.label v x) (D.label v y) ∧
    At P.Φ v (x + v.length - y)) ∨
  (∃ x < v.length, P.S (D.label v x) (D.label v v.length)) ∨
  (∃ x < v.length, P.S' (D.label v x) (D.label v v.length) ∧ At P.Φ v x)

/-- A positive hole: a hole with the positive condition. -/
def PosHole (D : Lettered Γ C) (P : PosChan Γ C) (v : List Γ) : Prop :=
  D.IsHole v ∧ Pos D P v

/-- The final test at a label, false at the start label. -/
def PosChan.FLab (P : PosChan Γ C) : Lab Γ C → Prop
  | none => False
  | some (c, a) => P.F c a

/-- The final test at a label is decidable. -/
instance PosChan.decFLab (P : PosChan Γ C) [∀ c a, Decidable (P.F c a)] :
    ∀ L, Decidable (P.FLab L)
  | none => isFalse id
  | some (c, a) => (inferInstance : Decidable (P.F c a))

/-- The positive condition with all quantifiers over bounded cuts. -/
theorem pos_iff_bounded (D : Lettered Γ C) (P : PosChan Γ C) (v : List Γ) :
    Pos D P v ↔
    P.FLab (D.label v v.length) ∨
    (∃ x < v.length, ∃ y < v.length, x < y ∧ v.drop y <+: v.drop x ∧
      P.R (D.label v x) (D.label v y) ∧ At P.Φ v (x + v.length - y)) ∨
    (∃ x < v.length, P.S (D.label v x) (D.label v v.length)) ∨
    (∃ x < v.length, P.S' (D.label v x) (D.label v v.length) ∧ At P.Φ v x) := by
  unfold Pos
  apply or_congr
  · cases D.label v v.length with
    | none => simp [PosChan.FLab]
    | some p => rcases p with ⟨c, a⟩; simp [PosChan.FLab]
  apply or_congr _ Iff.rfl
  constructor
  · rintro ⟨x, y, ⟨hxy, _, hp⟩, hy, hr, hφ⟩
    exact ⟨x, by omega, y, hy, hxy, hp, hr, hφ⟩
  · rintro ⟨x, _, y, hy, hxy, hp, hr, hφ⟩
    exact ⟨x, y, ⟨hxy, hy.le, hp⟩, hy, hr, hφ⟩

/-- The positive condition is decidable when the channel is. -/
instance decPos [DecidableEq Γ] (D : Lettered Γ C) (P : PosChan Γ C)
    [∀ c a, Decidable (P.F c a)] [DecidableRel P.R] [DecidableRel P.S]
    [DecidableRel P.S'] [DecidablePred P.Φ] (v : List Γ) : Decidable (Pos D P v) :=
  decidable_of_iff _ (pos_iff_bounded D P v).symm

/-- Positive holes are decidable when holes and the positive condition are. -/
instance decPosHole (D : Lettered Γ C) (P : PosChan Γ C) (v : List Γ)
    [Decidable (D.IsHole v)] [Decidable (Pos D P v)] : Decidable (PosHole D P v) :=
  inferInstanceAs (Decidable (D.IsHole v ∧ Pos D P v))

/-- Reader admissions are decidable when the relation is. -/
instance decReaderΛ (M : DFA Γ C) (R : C → C → Prop) [DecidableRel R] :
    ∀ L L', Decidable (readerΛ M R L L')
  | _, none => isFalse id
  | L, some p => (inferInstance : Decidable (R (stOf M L) (stOf M (some p))))

/-- The base channel of a reader: `Pi` on the states of the labels (false into the start
label), for both `R` and `S'`, with the separator as letter test. -/
def baseChan (M : DFA Γ C) (Pi : C → C → Prop) (sep : Γ) : PosChan Γ C where
  F _ _ := False
  R := readerΛ M Pi
  S _ _ := False
  S' := readerΛ M Pi
  Φ := (· = sep)

/-- The final test of the base channel is decidable. -/
instance decBaseF (M : DFA Γ C) (Pi : C → C → Prop) (sep : Γ) :
    ∀ c a, Decidable ((baseChan M Pi sep).F c a) :=
  fun _ _ => inferInstanceAs (Decidable False)

/-- The relation `R` of the base channel is decidable. -/
instance decBaseR (M : DFA Γ C) (Pi : C → C → Prop) [DecidableRel Pi] (sep : Γ) :
    DecidableRel (baseChan M Pi sep).R := decReaderΛ M Pi

/-- The relation `S` of the base channel is decidable. -/
instance decBaseS (M : DFA Γ C) (Pi : C → C → Prop) (sep : Γ) :
    DecidableRel (baseChan M Pi sep).S := fun _ _ => inferInstanceAs (Decidable False)

/-- The relation `S'` of the base channel is decidable. -/
instance decBaseS' (M : DFA Γ C) (Pi : C → C → Prop) [DecidableRel Pi] (sep : Γ) :
    DecidableRel (baseChan M Pi sep).S' := decReaderΛ M Pi

/-- The letter test of the base channel is decidable. -/
instance decBaseΦ [DecidableEq Γ] (M : DFA Γ C) (Pi : C → C → Prop) (sep : Γ) :
    DecidablePred (baseChan M Pi sep).Φ := fun _ => inferInstanceAs (Decidable (_ = sep))

/-- The base channel holds iff some comparison has its states in `Pi` and the separator as
continuation letter. -/
theorem pos_base_iff_comparison (M : DFA Γ C) (Adm Pi : C → C → Prop) (T : Set C)
    (sep : Γ) (w : List Γ) :
    Pos (ofReader M Adm T) (baseChan M Pi sep) w ↔
    ∃ s e, IsComp w s e ∧ Pi (runPrefix M w s) (runPrefix M w e) ∧
      w[s + w.length - e]? = some sep := by
  have rel : ∀ s e, s < e → e ≤ w.length →
      (readerΛ M Pi ((ofReader M Adm T).label w s) ((ofReader M Adm T).label w e) ↔
      Pi (runPrefix M w s) (runPrefix M w e)) := by
    intro s e hse he
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    have hl := Lettered.label_succ (ofReader M Adm T) w (by omega : j < w.length)
    have hst := stOf_label M Adm T w (j + 1) he
    rw [hl] at hst
    rw [hl, readerΛ, stOf_label M Adm T w s (by omega), hst]
  simp only [Pos, baseChan, and_false, exists_false, false_or, At,
    exists_eq_right]
  constructor
  · rintro (⟨s, e, hc, he, hr, ha⟩ | ⟨s, hs, hr, ha⟩)
    · exact ⟨s, e, hc, (rel s e hc.1 hc.2.1).mp hr, ha⟩
    · exact ⟨s, w.length, isComp_end w hs, (rel s _ hs le_rfl).mp hr, by simpa using ha⟩
  · rintro ⟨s, e, hc, hr, ha⟩
    rcases lt_or_eq_of_le hc.2.1 with he | rfl
    · exact Or.inl ⟨s, e, hc, he, (rel s e hc.1 hc.2.1).mpr hr, ha⟩
    · exact Or.inr ⟨s, hc.1, (rel s _ hc.1 le_rfl).mpr hr, by simpa using ha⟩

/-- A letter that occurs once has a unique position. -/
theorem unique_separator [DecidableEq Γ] (sep : Γ) (w : List Γ)
    (hc : w.count sep = 1) {p q : ℕ}
    (hp : w[p]? = some sep) (hq : w[q]? = some sep) : p = q := by
  induction w generalizing p q with
  | nil => simp at hp
  | cons a w ih =>
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst a
      have hn : sep ∉ w := List.not_mem_of_count_eq_zero (by simpa using hc)
      cases q with
      | zero => rfl
      | succ q => exact False.elim (hn (List.mem_of_getElem? hq))
    | succ p =>
      cases q with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst a
        have hn : sep ∉ w := List.not_mem_of_count_eq_zero (by simpa using hc)
        exact False.elim (hn (List.mem_of_getElem? hp))
      | succ q =>
        have hm : sep ∈ w := List.mem_of_getElem? hp
        have hpos := List.count_pos_iff.mpr hm
        have hcount : w.count sep = 1 := by
          rw [List.count_cons] at hc
          split at hc <;> omega
        exact congrArg Nat.succ (ih hcount hp hq)

/-- The anchored comparison `(s, e)` at the separator position `p`: `e = s + |w| - p`, and
the suffix at `e` is the factor from `s` to `p`. -/
def AnchoredAt (w : List Γ) (p s e : ℕ) : Prop :=
  s ≤ p ∧ e = s + w.length - p ∧ w.drop e = (w.drop s).take (p - s)

/-- A pair is anchored at `p` iff it is a comparison whose continuation letter is at `p`. -/
theorem anchoredAt_iff (w : List Γ) {p s e : ℕ} (hp : p < w.length) :
    AnchoredAt w p s e ↔ IsComp w s e ∧ s + w.length - e = p := by
  constructor
  · rintro ⟨hs, rfl, he⟩
    refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
    rw [he]
    exact List.take_prefix _ _
  · rintro ⟨⟨hse, he, hc⟩, hpos⟩
    refine ⟨by omega, by omega, ?_⟩
    have ht := List.prefix_iff_eq_take.mp hc
    simpa only [List.length_drop, show w.length - e = p - s by omega] using ht

/-- On a word with exactly one separator, at position `p`, the base channel holds iff some
comparison anchored at `p` has its states in `Pi`. -/
theorem pos_base_iff_anchored [DecidableEq Γ] (M : DFA Γ C)
    (Adm Pi : C → C → Prop) (T : Set C) (sep : Γ) (w : List Γ) (p : ℕ)
    (hc : w.count sep = 1) (hp : w[p]? = some sep) :
    Pos (ofReader M Adm T) (baseChan M Pi sep) w ↔
    ∃ s ≤ p, w.drop (s + w.length - p) = (w.drop s).take (p - s) ∧
      Pi (runPrefix M w s) (runPrefix M w (s + w.length - p)) := by
  have hplen : p < w.length := List.getElem?_eq_some_iff.mp hp |>.1
  rw [pos_base_iff_comparison]
  constructor
  · rintro ⟨s, e, hcomp, hPi, hsep⟩
    have hpos := unique_separator sep w hc hsep hp
    obtain ⟨hs, he, hw⟩ := (anchoredAt_iff w hplen).mpr ⟨hcomp, hpos⟩
    exact ⟨s, hs, he ▸ hw, he ▸ hPi⟩
  · rintro ⟨s, hs, hw, hPi⟩
    obtain ⟨hcomp, hpos⟩ := (anchoredAt_iff w hplen).mp ⟨hs, rfl, hw⟩
    exact ⟨s, _, hcomp, hPi, by rw [hpos]; exact hp⟩

end DeciENSSE.Anchored
