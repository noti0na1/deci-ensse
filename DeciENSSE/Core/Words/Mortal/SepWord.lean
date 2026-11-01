import DeciENSSE.Core.Words.SS2
import DeciNSSE.Holes.CoAlignment

/-! # Separator words and anchored comparisons

A pair of words `(u, t)` is encoded as the separator word `u ♯ t` over `Option α`, with
`none` as the separator `♯`. No comparison ends at or before the separator. A comparison
across it is a cross comparison of the pair, and it is anchored, that is, its matched factor
ends right before the separator, exactly when the suffixes of `u` and `t` at its cuts are
equal. Words with exactly one separator are exactly the separator words.

## Main declarations

- `sepWord`: the separator word of a pair.
- `no_pre_comparison`, `cross_comparison_iff`: comparisons of a separator word.
- `Anchored`, `anchored_iff`, `anchored_target`: anchored comparisons and aligned cuts.
- `separator_unique`, `exists_sepWord`: the separator position, and words with one
  separator.

The declarations are in the namespace `DeciENSSE.Core.Mortal`.
-/

namespace DeciENSSE.Core.Mortal

variable {α : Type*}
open DeciNSSE.CoAlignment

/-- The separator word `u ♯ t`, with `none` as the separator. -/
def sepWord (u t : Word α) : List (Option α) := u.map some ++ none :: t.map some

/-- The length of a separator word. -/
@[simp] theorem length_sepWord (u t : Word α) :
    (sepWord u t).length = u.length + 1 + t.length := by simp [sepWord]; omega

/-- Separator words are nonempty. -/
@[simp] theorem sepWord_ne_nil (u t : Word α) : sepWord u t ≠ [] := by simp [sepWord]

/-- A separator word has exactly one separator. -/
@[simp] theorem count_sepWord [DecidableEq α] (u t : Word α) : (sepWord u t).count none = 1 := by
  have h (v : Word α) : (v.map some).count none = 0 := by
    induction v with
    | nil => rfl
    | cons a v ih => simpa using ih
  simp [sepWord, h]

/-- A prefix that ends in the spine is a prefix of the spine. -/
theorem take_spine (u t : Word α) {s : ℕ} (hs : s ≤ u.length) :
    (sepWord u t).take s = (u.take s).map some := by
  unfold sepWord
  rw [List.take_append_of_le_length (by simpa using hs), ← List.map_take]

/-- A suffix that starts in the spine is the separator word of the spine suffix. -/
theorem drop_spine (u t : Word α) {s : ℕ} (hs : s ≤ u.length) :
    (sepWord u t).drop s = sepWord (u.drop s) t := by
  unfold sepWord
  rw [List.drop_append_of_le_length (by simpa using hs), ← List.map_drop]

/-- A suffix that starts after the separator is a suffix of the target. -/
@[simp] theorem drop_target (u t : Word α) (e : ℕ) :
    (sepWord u t).drop (u.length + 1 + e) = (t.drop e).map some := by
  unfold sepWord
  rw [List.drop_append]
  simp [List.drop_eq_nil_of_le (by simp; omega : (u.map some).length ≤ u.length + 1 + e),
    show u.length + 1 + e - u.length = e + 1 by omega,
    ← List.map_drop]

/-- A prefix that ends after the separator is the separator word of a target prefix. -/
theorem take_target (u t : Word α) (e : ℕ) :
    (sepWord u t).take (u.length + 1 + e) = sepWord u (t.take e) := by
  unfold sepWord
  rw [List.take_append]
  simp [List.take_of_length_le (by simp; omega : (u.map some).length ≤ u.length + 1 + e),
    show u.length + 1 + e - u.length = e + 1 by omega,
    ← List.map_take]

/-- The factor from a spine cut to the separator is the spine suffix. -/
theorem spine_factor (u t : Word α) {s : ℕ} (hs : s ≤ u.length) :
    ((sepWord u t).drop s).take (u.length - s) = (u.drop s).map some := by
  rw [drop_spine u t hs]
  have h := take_spine (u.drop s) t (s := (u.drop s).length) le_rfl
  rw [List.take_length] at h
  simpa only [List.length_drop] using h

/-- A word without separator is a prefix of `u ♯ t` iff it is a prefix of `u`. -/
theorem binary_prefix_sep (v u t : Word α) :
    v.map some <+: sepWord u t ↔ v <+: u := by
  induction v generalizing u with
  | nil => simp
  | cons a v ih =>
    cases u with
    | nil => simp [sepWord]
    | cons b u =>
      change (some a :: v.map some <+: some b :: sepWord u t) ↔ _
      simp only [List.cons_prefix_cons, Option.some.injEq]
      exact and_congr Iff.rfl (ih u)

/-- Separator words are prefixes of each other iff their spines are equal and their
targets are prefixes. -/
theorem sep_prefix_sep (u t v z : Word α) :
    sepWord u t <+: sepWord v z ↔ u = v ∧ t <+: z := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [sepWord, List.prefix_map_iff_of_injective (Option.some_injective _)]
    | cons b v => simp [sepWord]
  | cons a u ih =>
    cases v with
    | nil => simp [sepWord]
    | cons b v =>
      change (some a :: sepWord u t <+: some b :: sepWord v z) ↔ _
      simp only [List.cons_prefix_cons, Option.some.injEq, List.cons.injEq, ih, and_assoc]

/-- No comparison ends at or before the separator. -/
theorem no_pre_comparison (u t : Word α) {s e : ℕ} (hse : s < e)
    (he : e ≤ u.length) : ¬ IsComp (sepWord u t) s e := by
  rintro ⟨_, _, hp⟩
  rw [drop_spine u t he, drop_spine u t (by omega), sep_prefix_sep] at hp
  have := congrArg List.length hp.1
  simp only [List.length_drop] at this
  omega

/-- Comparisons across the separator are the cross comparisons of the pair. -/
theorem cross_comparison_iff (u t : Word α) {s e : ℕ}
    (hs : s ≤ u.length) (he : e ≤ t.length) :
    IsComp (sepWord u t) s (u.length + 1 + e) ↔ t.drop e <+: u.drop s := by
  simp only [IsComp, length_sepWord, drop_target, drop_spine u t hs,
    binary_prefix_sep]
  simp only [show s < u.length + 1 + e by omega,
    show u.length + 1 + e ≤ u.length + 1 + t.length by omega, true_and]

/-- The anchored comparison `(s, e)` at the separator position `p`: `e = s + |w| - p`, and the
suffix at `e` is the factor from `s` to `p`. -/
def Anchored (w : List (Option α)) (p s e : ℕ) : Prop :=
  s ≤ p ∧ e = s + w.length - p ∧ w.drop e = (w.drop s).take (p - s)

/-- Anchored pairs are comparisons. -/
theorem Anchored.isComp {w : List (Option α)} {p s e : ℕ}
    (hp : p < w.length) (h : Anchored w p s e) : IsComp w s e := by
  refine ⟨by obtain ⟨_, _, _⟩ := h; omega, by obtain ⟨_, _, _⟩ := h; omega, ?_⟩
  rw [h.2.2]
  exact List.take_prefix _ _

/-- A pair of cuts across the separator is anchored iff the suffixes of the spine and the
target at these cuts are equal. -/
theorem anchored_iff (u t : Word α) {s e : ℕ}
    (hs : s ≤ u.length) (he : e ≤ t.length) :
    Anchored (sepWord u t) u.length s (u.length + 1 + e) ↔
      u.drop s = t.drop e := by
  rw [Anchored, drop_target, spine_factor u t hs]
  constructor
  · intro h
    exact (List.map_injective_iff.mpr (Option.some_injective _) h.2.2).symm
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_drop] at hl
    exact ⟨hs, by simp only [length_sepWord]; omega, congrArg (List.map some) h.symm⟩

/-- Every anchored comparison crosses the separator at aligned cuts. -/
theorem anchored_target (u t : Word α) {s e : ℕ}
    (h : Anchored (sepWord u t) u.length s e) :
    ∃ j ≤ t.length, e = u.length + 1 + j ∧ u.drop s = t.drop j := by
  have hc := h.isComp (by simp only [length_sepWord]; omega)
  have he : u.length < e := by
    by_contra hn
    exact no_pre_comparison u t hc.1 (by omega) hc
  have hj : e - (u.length + 1) ≤ t.length := by
    have := hc.2.1; simp only [length_sepWord] at this; omega
  have eq : e = u.length + 1 + (e - (u.length + 1)) := by omega
  exact ⟨_, hj, eq, (anchored_iff u t h.1 hj).mp (eq ▸ h)⟩

/-- The separator occurs only after the spine. -/
theorem separator_unique (u t : Word α) (p : ℕ) :
    (sepWord u t)[p]? = some none ↔ p = u.length := by
  induction u generalizing p with
  | nil =>
    cases p with
    | zero => simp [sepWord]
    | succ p => simp [sepWord, List.getElem?_map]
  | cons a u ih =>
    cases p with
    | zero => simp [sepWord]
    | succ p => simpa only [sepWord, List.map_cons, List.cons_append,
        List.getElem?_cons_succ, List.length_cons, Nat.succ.injEq] using ih p

/-- A word without separator is the image of a word over `α`. -/
theorem plain_of_no_separator [DecidableEq α] (w : List (Option α)) (h : w.count none = 0) :
    ∃ u : Word α, w = u.map some := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
    cases a with
    | none => simp at h
    | some a =>
      obtain ⟨u, rfl⟩ := ih (by simpa using h)
      exact ⟨a :: u, rfl⟩

/-- A word with exactly one separator is a separator word. -/
theorem exists_sepWord [DecidableEq α] (w : List (Option α)) (h : w.count none = 1) :
    ∃ u t, w = sepWord u t := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    cases a with
    | none =>
      obtain ⟨t, rfl⟩ := plain_of_no_separator w (by simpa using h)
      exact ⟨[], t, rfl⟩
    | some a =>
      obtain ⟨u,t,rfl⟩ := ih (by simpa using h)
      exact ⟨a :: u, t, rfl⟩

end DeciENSSE.Core.Mortal
