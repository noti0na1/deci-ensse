import Mathlib.Tactic.GCongr
import DeciENSSE.Core.Words.Periodic
import DeciENSSE.Core.Words.NonMortalBound

/-! # Pumping purely periodic pre-holes

Deleting factors between matching reader states preserves safety, rejection,
a head witness, and survivor freeness. Six deletion cases bound the periodic
ends and rests independently of the alphabet.

## Main declarations

- `SS2.pumpGood_delete`
- `SS2.pumpGood_short`
- `nonMortalShortHoleBound_pump`
- `nonMortalShortHoleBound_poly`
-/

namespace DeciENSSE.Core

variable {α : Type*}

/-! ## Infinite words that are not proper self-extensions -/

/-- No nonempty finite word extends `X` to itself. -/
def NonSelfSimilar (X : ℕ → α) : Prop := ∀ z : Word α, z ≠ [] → prepend z X ≠ X

/-- A stream is reconstructed from a prefix and the remaining suffix. -/
theorem prepend_streamPrefix_shift (X : ℕ → α) (k : ℕ) :
    prepend (streamPrefix X k) (fun i => X (k + i)) = X := by
  funext i
  by_cases hi : i < k
  · simp [prepend, hi]
  · simp [prepend, hi, Nat.add_sub_cancel' (by omega : k ≤ i)]

/-- Shifting a prepended stream past the word recovers the original stream. -/
theorem shift_prepend_self (a : Word α) (X : ℕ → α) :
    (fun i => prepend a X (a.length + i)) = X := by
  funext i; simp [prepend]

/-- Non-self-similarity makes prepending injective in the finite prefix. -/
theorem NonSelfSimilar.prepend_inj {X : ℕ → α} (hX : NonSelfSimilar X) {x y : Word α}
    (h : prepend x X = prepend y X) : x = y := by
  rcases le_total y.length x.length with hl | hl
  · obtain ⟨r, rfl, hr⟩ := prepend_factor hl h
    by_cases hr0 : r = []
    · simp [hr0]
    · exact (hX r hr0 hr).elim
  · obtain ⟨r, rfl, hr⟩ := prepend_factor hl h.symm
    by_cases hr0 : r = []
    · simp [hr0]
    · exact (hX r hr0 hr).elim

/-- A non-self-similar word is not a proper extension of one of its own shifts. -/
theorem NonSelfSimilar.ne_shift {X : ℕ → α} (hX : NonSelfSimilar X) {z : Word α}
    (hz : z ≠ []) (k : ℕ) : prepend z X ≠ fun i => X (k + i) := by
  intro h
  apply hX (streamPrefix X k ++ z) (by simp [hz])
  rw [prepend_assoc, h, prepend_streamPrefix_shift]

/-- Splitting an equation of prefixed infinite words at the shorter prefix. -/
theorem prepend_eq_prepend_le {a b : Word α} {X Y : ℕ → α} (hl : a.length ≤ b.length)
    (h : prepend a X = prepend b Y) :
    a = b.take a.length ∧ X = prepend (b.drop a.length) Y := by
  constructor
  · have h1 := congrArg (fun f => streamPrefix f a.length) h
    simp only [prepend_prefix] at h1
    exact h1.trans (prepend_streamPrefix (prepend_prefix b Y) hl)
  · have h2 := congrArg (fun f => fun i => f (a.length + i)) h
    simp only [shift_prepend_self] at h2
    rw [h2, prepend_shift b Y hl]

/-- Dropping within a split word preserves the remaining factors. -/
theorem drop_split (t : Word α) {e e' : ℕ} (h : e ≤ e') :
    t.drop e = (t.drop e).take (e' - e) ++ t.drop e' := by
  conv_lhs => rw [← List.take_append_drop (e' - e) (t.drop e)]
  rw [List.drop_drop, Nat.add_sub_cancel' h]

/-- Two cuts of one word with the same non-self-similar infinite suffix coincide. -/
theorem cut_unique {ξ : ℕ → α} {t : Word α} {e e₁ : ℕ}
    (hX : NonSelfSimilar (prepend (t.drop e₁) ξ)) (he : e ≤ t.length) (he₁ : e₁ ≤ t.length)
    (h : prepend (t.drop e) ξ = prepend (t.drop e₁) ξ) : e = e₁ := by
  rcases lt_trichotomy e e₁ with hlt | heq | hgt
  · exfalso
    rw [drop_split t hlt.le, prepend_assoc] at h
    exact hX _ (by
      intro hn
      have := congrArg List.length hn
      simp at this; omega) h
  · exact heq
  · exfalso
    have h2 : prepend (t.drop e₁) ξ =
        prepend ((t.drop e₁).take (e - e₁)) (prepend (t.drop e₁) ξ) := by
      conv_lhs => rw [drop_split t hgt.le]
      rw [prepend_assoc, h]
    apply hX ((t.drop e₁).take (e - e₁)) (by
      intro hn
      have := congrArg List.length hn
      simp at this; omega)
    exact h2.symm

/-- Every cut in the rest has a non-self-similar infinite suffix. -/
theorem nonSelfSimilar_of_rest {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p)
    {w : Word α} {r s : ℕ} (hw : PeriodicSplit ξ p w r) (hs : s < r) :
    NonSelfSimilar (prepend (w.drop s) ξ) := by
  intro z hz h
  have hper : StreamPeriod (prepend (w.drop s) ξ) z.length :=
    ((prepend_fixed_iff_prefix_period z).mp h).2
  have hsuf : StreamPeriod (fun i => prepend (w.drop s) ξ ((w.drop s).length + i)) p := by
    rw [shift_prepend_self]; exact hp.2.1
  have hp' := period_of_suffix (List.length_pos_iff.mpr hz) hper hsuf
  have := (hw.periodic_iff (by have := hw.le_length; omega)).mp hp'
  omega

/-- Cuts of a periodic end with equal residues have equal infinite suffixes. -/
theorem PeriodicSplit.cut_eq {ξ : ℕ → α} {p : ℕ} {w : Word α} {r : ℕ}
    (hp : LeastStreamPeriod ξ p) (hw : PeriodicSplit ξ p w r)
    {s s' : ℕ} (hs : r ≤ s) (hs' : r ≤ s') (hsl : s ≤ w.length) (hsl' : s' ≤ w.length)
    (hmod : (w.length - s) % p = (w.length - s') % p) :
    prepend (w.drop s) ξ = prepend (w.drop s') ξ := by
  apply (periodic_ends_eq_iff hp ((hw.periodic_iff hsl).mpr hs)
    ((hw.periodic_iff hsl').mpr hs')).mpr
  simpa using hmod

/-! ## Reader states after deleting a factor -/

theorem LDFA.atCut_append_right {S : Type*} (M : LDFA α S) (x z : Word α) (k : ℕ) :
    M.atCut (x ++ z) (x.length + k) = M.runFrom (M.run x) (z.take k) := by
  simp [LDFA.atCut, LDFA.run, List.take_length_add_append, LDFA.runFrom_append]

/-- Running a concatenation continues from the state reached by the first word. -/
theorem LDFA.run_append {S : Type*} (M : LDFA α S) (x z : Word α) :
    M.run (x ++ z) = M.runFrom (M.run x) z := by
  simp [LDFA.run, LDFA.runFrom_append]

/-- Deleting a loop preserves the state at a corresponding cut. -/
theorem LDFA.atCut_delete {S : Type*} (M : LDFA α S) {x w : Word α} (y : Word α)
    (hM : M.runFrom (M.run x) w = M.run x) (k : ℕ) :
    M.atCut (x ++ w ++ y) (x.length + w.length + k) = M.atCut (x ++ y) (x.length + k) := by
  have h1 : x ++ w ++ y = (x ++ w) ++ y := by simp
  rw [h1, show x.length + w.length + k = (x ++ w).length + k by simp,
    LDFA.atCut_append_right, LDFA.atCut_append_right, LDFA.run_append, hM]

/-- Deleting a later factor leaves earlier cut states unchanged. -/
theorem LDFA.atCut_delete_left {S : Type*} (M : LDFA α S) {x : Word α} (w y : Word α)
    {s : ℕ} (hs : s ≤ x.length) :
    M.atCut (x ++ w ++ y) s = M.atCut (x ++ y) s := by
  rw [LDFA.atCut_append _ _ _ (by simp; omega : s ≤ (x ++ w).length),
    LDFA.atCut_append _ _ _ hs, LDFA.atCut_append _ _ _ hs]

/-- A suffix beginning before a deleted factor has the corresponding factorization. -/
theorem drop_delete_left {x : Word α} (w y : Word α) {s : ℕ} (hs : s ≤ x.length) :
    (x ++ w ++ y).drop s = x.drop s ++ w ++ y := by
  rw [List.drop_append_of_le_length (by simp; omega : s ≤ (x ++ w).length),
    List.drop_append_of_le_length hs]

/-- A suffix beginning after a deleted factor is unchanged after shifting its cut. -/
theorem drop_delete_right (x w y : Word α) (k : ℕ) :
    (x ++ w ++ y).drop (x.length + w.length + k) = y.drop k := by
  rw [show x.length + w.length + k = (x ++ w).length + k by simp,
    List.drop_length_add_append]

/-- Deleting a factor between equal reader states preserves the final state. -/
theorem LDFA.run_delete {S : Type*} (M : LDFA α S) {x w : Word α} (y : Word α)
    (hM : M.runFrom (M.run x) w = M.run x) :
    M.run (x ++ w ++ y) = M.run (x ++ y) := by
  rw [show x ++ w ++ y = (x ++ w) ++ y by simp, LDFA.run_append, LDFA.run_append,
    LDFA.run_append, hM, ← LDFA.run_append]

namespace SS2
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-! ## Survivor-free pre-holes as one predicate -/

/-- The guard test of `survivorFree_iff_suffix_guard`. It also covers all
aligned cut pairs. -/
def SuffixGuardFree (ξ : ℕ → α) (u t : Word α) : Prop :=
  ∀ s ≤ u.length, ∀ e ≤ t.length, t.length - e ≤ u.length - s →
    prepend (u.drop s) ξ = prepend (t.drop e) ξ → (I.A.atCut u s, I.B.atCut t e) ∉ I.Guard

/-- A pre-hole for which `ξ` is survivor-free, unfolded for pumping. -/
def PumpGood (ξ : ℕ → α) (u t : Word α) : Prop :=
  I.SafeFrom I.A.start u ∧ I.TargetOpen t ∧ I.B.run t ∈ I.Rej ∧
    I.HasHeadEvent u t ∧ I.SuffixGuardFree ξ u t

/-- Rejection exactly at the endpoint is unrejection at every earlier cut. -/
theorem J_eq_length_iff (t : Word α) :
    I.J t = some t.length ↔ I.B.run t ∈ I.Rej ∧ I.TargetOpen t := by
  simpa [LDFA.atCut, TargetOpen] using I.J_eq_some_iff t t.length

/-- The pumping invariant is a pre-hole with a survivor-free periodic continuation. -/
theorem pumpGood_iff [Inhabited α] (ξ : ℕ → α) (u t : Word α) :
    I.PumpGood ξ u t ↔ I.IsPreHole u t ∧ I.SurvivorFree u t ξ := by
  constructor
  · rintro ⟨hs, ho, hr, hh, hg⟩
    have hj := (I.J_eq_length_iff t).mpr ⟨hr, ho⟩
    refine ⟨⟨hs, hj, hh, ?_⟩, (I.survivorFree_iff_suffix_guard hj).mpr hg⟩
    rintro s hs' e he' ⟨⟨_, _, hgd⟩, hal⟩
    have hlen := congrArg List.length hal.2.2
    simp only [List.length_drop] at hlen
    exact hg s hal.1 e hal.2.1 (by omega) (by rw [hal.2.2]) hgd
  · rintro ⟨⟨hs, hj, hh, _⟩, hf⟩
    obtain ⟨hr, ho⟩ := (I.J_eq_length_iff t).mp hj
    exact ⟨hs, ho, hr, hh, (I.survivorFree_iff_suffix_guard hj).mp hf⟩

/-- Aligned cuts have equal remaining depths. -/
theorem aligned_depth {u t : Word α} {s e : ℕ} (h : Aligned u t s e) :
    u.length - s = t.length - e := by
  have := congrArg List.length h.2.2
  simpa using this

/-! ## The generic deletion lemma -/

/-- Deleting `w` from `u = x w y` and `w'` from `t = x' w' y'`. The three
hypotheses `hDD`, `hDS`, `hSD` say that a suffix-equal pair of cuts of the
shortened words, with nonnegative offset, whose cuts are deep (in `x`) or
shallow (in `y`), comes from such a pair of the original words. The case of
two shallow cuts is automatic. -/
theorem pumpGood_delete {ξ : ℕ → α} {x w y x' w' y' : Word α}
    (hg : I.PumpGood ξ (x ++ w ++ y) (x' ++ w' ++ y'))
    (hA : I.A.runFrom (I.A.run x) w = I.A.run x)
    (hA' : I.A'.runFrom (I.A'.run x) w = I.A'.run x)
    (hB : I.B.runFrom (I.B.run x') w' = I.B.run x')
    (hB' : I.B'.runFrom (I.B'.run x') w' = I.B'.run x')
    (hDD : ∀ s < x.length, ∀ e < x'.length,
      x'.length - e + y'.length ≤ x.length - s + y.length →
      prepend (x.drop s ++ y) ξ = prepend (x'.drop e ++ y') ξ →
      x'.length - e + w'.length + y'.length ≤ x.length - s + w.length + y.length ∧
      prepend (x.drop s ++ w ++ y) ξ = prepend (x'.drop e ++ w' ++ y') ξ)
    (hDS : ∀ s < x.length, ∀ k ≤ y'.length,
      y'.length - k ≤ x.length - s + y.length →
      prepend (x.drop s ++ y) ξ = prepend (y'.drop k) ξ →
      prepend (x.drop s ++ w ++ y) ξ = prepend (y'.drop k) ξ)
    (hSD : ∀ k ≤ y.length, ∀ e < x'.length,
      x'.length - e + y'.length ≤ y.length - k →
      prepend (y.drop k) ξ = prepend (x'.drop e ++ y') ξ →
      x'.length - e + w'.length + y'.length ≤ y.length - k ∧
      prepend (y.drop k) ξ = prepend (x'.drop e ++ w' ++ y') ξ)
    (hhead : ∃ s e, I.HeadEvent (x ++ w ++ y) (x' ++ w' ++ y') s e ∧
      ((x.length + w.length ≤ s ∧ x'.length + w'.length ≤ e) ∨
        (s ≤ x.length ∧ e ≤ x'.length ∧ x.length - s = x'.length - e ∧
          w.length = w'.length))) :
    I.PumpGood ξ (x ++ y) (x' ++ y') := by
  obtain ⟨hsafe, hopen, hrej, _, hsg⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- safety
    have h1 := I.safeFrom_append.mp hsafe
    have h2 := I.safeFrom_append.mp h1.1
    refine I.safeFrom_append.mpr ⟨h2.1, ?_⟩
    have h3 := h1.2
    rw [LDFA.runFrom_append] at h3
    change I.SafeFrom (I.A.runFrom (I.A.run x) w) y at h3
    rw [hA] at h3
    exact h3
  · -- the target has no proper rejecting cut
    intro i hi
    simp only [List.length_append] at hi
    by_cases hix : i ≤ x'.length
    · rw [← I.B.atCut_delete_left w' y' hix]
      exact hopen i (by simp; omega)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : x'.length ≤ i)
      rw [← I.B.atCut_delete y' hB k]
      exact hopen _ (by simp; omega)
  · rwa [← I.B.run_delete y' hB]
  · -- head event
    obtain ⟨s, e, ⟨⟨hs, he, hal⟩, hhd⟩, hsh | ⟨hsx, hex, hlen, hw⟩⟩ := hhead
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hsh.1
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hsh.2
      refine ⟨x.length + k, by simp at hs ⊢; omega, x'.length + k', by simp at he ⊢; omega,
        ⟨by simp at hs ⊢; omega, by simp at he ⊢; omega, ?_⟩, ?_⟩
      · rw [List.drop_length_add_append, List.drop_length_add_append,
          ← drop_delete_right x w y k, ← drop_delete_right x' w' y' k', hal]
      · rwa [← I.A'.atCut_delete y hA' k, ← I.B'.atCut_delete y' hB' k']
    · refine ⟨s, by simp; omega, e, by simp; omega, ⟨by simp; omega, by simp; omega, ?_⟩, ?_⟩
      · rw [drop_delete_left w y hsx, drop_delete_left w' y' hex] at hal
        obtain ⟨h12, h3⟩ := List.append_inj hal (by simp; omega)
        obtain ⟨h1, _⟩ := List.append_inj h12 (by simp; omega)
        rw [List.drop_append_of_le_length hsx, List.drop_append_of_le_length hex, h1, h3]
      · rwa [← I.A'.atCut_delete_left w y hsx, ← I.B'.atCut_delete_left w' y' hex]
  · -- suffix guard
    intro s hs e he hdep hsuf hgd
    simp only [List.length_append] at hs he hdep
    by_cases hsx : s < x.length
    · by_cases hex : e < x'.length
      · rw [List.drop_append_of_le_length hsx.le, List.drop_append_of_le_length hex.le] at hsuf
        obtain ⟨hdep', hsuf'⟩ := hDD s hsx e hex (by omega) hsuf
        apply hsg s (by simp; omega) e (by simp; omega) (by simp; omega)
          (by rw [drop_delete_left w y hsx.le, drop_delete_left w' y' hex.le]
              exact hsuf')
        rwa [I.A.atCut_delete_left w y hsx.le, I.B.atCut_delete_left w' y' hex.le]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hex)
        rw [List.drop_append_of_le_length hsx.le, List.drop_length_add_append] at hsuf
        have hsuf' := hDS s hsx k (by omega) (by omega) hsuf
        apply hsg s (by simp; omega) (x'.length + w'.length + k) (by simp; omega)
          (by simp; omega)
          (by
            rw [drop_delete_left w y hsx.le, drop_delete_right]
            exact hsuf')
        rwa [I.A.atCut_delete_left w y hsx.le, I.B.atCut_delete y' hB k]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hsx)
      by_cases hex : e < x'.length
      · rw [List.drop_length_add_append, List.drop_append_of_le_length hex.le] at hsuf
        obtain ⟨hdep', hsuf'⟩ := hSD k (by omega) e hex (by omega) hsuf
        apply hsg (x.length + w.length + k) (by simp; omega) e (by simp; omega)
          (by simp; omega)
          (by
            rw [drop_delete_left w' y' hex.le, drop_delete_right]
            exact hsuf')
        rwa [I.A.atCut_delete y hA k, I.B.atCut_delete_left w' y' hex.le]
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hex)
        rw [List.drop_length_add_append, List.drop_length_add_append] at hsuf
        apply hsg (x.length + w.length + k) (by simp; omega) (x'.length + w'.length + k')
          (by simp; omega) (by simp; omega)
          (by
            rw [drop_delete_right, drop_delete_right]
            exact hsuf)
        rwa [I.A.atCut_delete y hA k, I.B.atCut_delete y' hB k']


/-! ## Cut-and-paste toolkit -/

/-- The result of one successful deletion. -/
def Shrinks (ξ : ℕ → α) (u t : Word α) : Prop :=
  ∃ u' t', I.PumpGood ξ u' t' ∧ I.A.run u' = I.A.run u ∧
    u'.length + t'.length < u.length + t.length

/-- Some head pair has its spine cut at `c` or later. -/
def HeadFrom (u t : Word α) (c : ℕ) : Prop := ∃ s e, c ≤ s ∧ I.HeadEvent u t s e

/-- `pumpGood_delete`, packaged with the decomposition equations. -/
theorem shrink_of_delete {ξ : ℕ → α} {u t x w y x' w' y' : Word α}
    (hu : x ++ w ++ y = u) (ht : x' ++ w' ++ y' = t) (hpos : w ≠ [] ∨ w' ≠ [])
    (hg : I.PumpGood ξ u t)
    (hA : I.A.runFrom (I.A.run x) w = I.A.run x)
    (hA' : I.A'.runFrom (I.A'.run x) w = I.A'.run x)
    (hB : I.B.runFrom (I.B.run x') w' = I.B.run x')
    (hB' : I.B'.runFrom (I.B'.run x') w' = I.B'.run x')
    (hDD : ∀ s < x.length, ∀ e < x'.length,
      x'.length - e + y'.length ≤ x.length - s + y.length →
      prepend (x.drop s ++ y) ξ = prepend (x'.drop e ++ y') ξ →
      x'.length - e + w'.length + y'.length ≤ x.length - s + w.length + y.length ∧
      prepend (x.drop s ++ w ++ y) ξ = prepend (x'.drop e ++ w' ++ y') ξ)
    (hDS : ∀ s < x.length, ∀ k ≤ y'.length,
      y'.length - k ≤ x.length - s + y.length →
      prepend (x.drop s ++ y) ξ = prepend (y'.drop k) ξ →
      prepend (x.drop s ++ w ++ y) ξ = prepend (y'.drop k) ξ)
    (hSD : ∀ k ≤ y.length, ∀ e < x'.length,
      x'.length - e + y'.length ≤ y.length - k →
      prepend (y.drop k) ξ = prepend (x'.drop e ++ y') ξ →
      x'.length - e + w'.length + y'.length ≤ y.length - k ∧
      prepend (y.drop k) ξ = prepend (x'.drop e ++ w' ++ y') ξ)
    (hhead : ∃ s e, I.HeadEvent u t s e ∧
      ((x.length + w.length ≤ s ∧ x'.length + w'.length ≤ e) ∨
        (s ≤ x.length ∧ e ≤ x'.length ∧ x.length - s = x'.length - e ∧
          w.length = w'.length))) :
    I.Shrinks ξ u t := by
  subst hu ht
  refine ⟨x ++ y, x' ++ y', I.pumpGood_delete hg hA hA' hB hB' hDD hDS hSD hhead,
    (I.A.run_delete y hA).symm, ?_⟩
  simp only [List.length_append]
  rcases hpos with h | h
  · have := List.length_pos_iff.mpr h; omega
  · have := List.length_pos_iff.mpr h; omega

end SS2

/-- Three-part decomposition of a word at two cuts. -/
theorem exists_split3 (u : Word α) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ u.length) :
    ∃ x w : Word α, x ++ w ++ u.drop j = u ∧ x.length = i ∧ w.length = j - i := by
  refine ⟨u.take i, (u.drop i).take (j - i), ?_, by simp; omega, by simp; omega⟩
  rw [List.append_assoc, ← drop_split u hij, List.take_append_drop]

/-- Running a factor starts from the reader state at its initial cut. -/
theorem LDFA.runFrom_of_atCut {S : Type*} (M : LDFA α S) {x w y u : Word α}
    (hu : x ++ w ++ y = u) {i j : ℕ} (hi : x.length = i) (hj : x.length + w.length = j)
    (h : M.atCut u i = M.atCut u j) : M.runFrom (M.run x) w = M.run x := by
  subst hu hi hj
  have h1 : M.atCut (x ++ w ++ y) x.length = M.run x := by
    rw [LDFA.atCut_delete_left M w y le_rfl, ← Nat.add_zero x.length,
      LDFA.atCut_append_right]
    simp [LDFA.runFrom]
  have h2 : M.atCut (x ++ w ++ y) (x.length + w.length) = M.runFrom (M.run x) w := by
    rw [show x ++ w ++ y = (x ++ w) ++ y from rfl,
      LDFA.atCut_append _ _ _ (by simp : x.length + w.length ≤ (x ++ w).length),
      LDFA.atCut_append_right]
    simp
  rw [← h2, ← h]
  exact h1

/-- Prepending a middle factor reconstructs the corresponding stream suffix. -/
theorem prepend_mid {ξ : ℕ → α} {w y : Word α}
    (hW : prepend w (prepend y ξ) = prepend y ξ) (a : Word α) :
    prepend (a ++ w ++ y) ξ = prepend (a ++ y) ξ := by
  rw [prepend_assoc, prepend_assoc, hW, ← prepend_assoc]

/-- The suffix at the first cut of a three-part decomposition. -/
theorem drop_mid_eq {x w y u : Word α} (hu : x ++ w ++ y = u) :
    u.drop x.length = w ++ y := by
  rw [← hu, drop_delete_left w y le_rfl]; simp

/-- Pigeonhole on an initial segment of the naturals. -/
theorem exists_lt_map_eq {β : Type*} [Fintype β] (S : ℕ) (f : ℕ → β)
    (h : Fintype.card β ≤ S) : ∃ x y, x < y ∧ y ≤ S ∧ f x = f y := by
  obtain ⟨x, y, hne, hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (S + 1) => f i) (by simp; omega)
  have hx := x.isLt
  have hy := y.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact ⟨x, y, hlt, by omega, hxy⟩
  · exact ⟨y, x, hlt, by omega, hxy.symm⟩

/-- Pigeonhole on a finite set of naturals. -/
theorem exists_lt_map_eq_finset {β : Type*} [Fintype β] (s : Finset ℕ) (f : ℕ → β)
    (h : Fintype.card β < s.card) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y := by
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := Finset.univ) (by simpa using h) (f := f)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨x, hx, y, hy, hlt, hxy⟩
  · exact ⟨y, hy, x, hx, hlt, hxy.symm⟩

namespace SS2

/-! ## Structure of suffix-equal cut pairs -/

theorem aligned_shift {v v' : Word α} {s e j : ℕ} (h : Aligned v v' s e) (hsj : s ≤ j)
    (hj : j ≤ v.length) :
    e + (j - s) ≤ v'.length ∧ v.drop j = v'.drop (e + (j - s)) := by
  have hd := aligned_depth h
  refine ⟨by have := h.2.1; omega, ?_⟩
  have : v.drop j = (v.drop s).drop (j - s) := by rw [List.drop_drop, Nat.add_sub_cancel' hsj]
  rw [this, h.2.2, List.drop_drop]

/-- Alignment is symmetric under swapping the compared words and cuts. -/
theorem aligned_symm {v v' : Word α} {s e : ℕ} (h : Aligned v v' s e) : Aligned v' v e s :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

variable {ξ : ℕ → α} {p : ℕ}

/-- Away from equal periodic-end lengths, aligned cuts lie in both periodic ends. -/
theorem aligned_le_min (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt s e : ℕ}
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (hne : u.length - ru ≠ t.length - rt) (hal : Aligned u t s e) :
    u.length - s ≤ u.length - ru ∧ u.length - s ≤ t.length - rt := by
  have hd := aligned_depth hal
  have hs := hal.1
  have he := hal.2.1
  have h := (PeriodicSplit.aligned_suffix_eq_iff (k := u.length - s) hp hu ht (by omega)
    (by omega)).mp (by
      rw [show u.length - (u.length - s) = s by omega,
        show t.length - (u.length - s) = e by omega]
      exact hal.2.2)
  rcases h with h | h
  · exact ⟨le_trans h (min_le_left _ _), le_trans h (min_le_right _ _)⟩
  · exact absurd h.1 hne

/-- A spine rest cut and its partner. -/
theorem partner_eq {u t : Word α} {ru rt : ℕ} (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ
  p t rt) {j e : ℕ}
    (hj : j < ru) (he : e ≤ t.length)
    (h : prepend (u.drop j) ξ = prepend (t.drop e) ξ) : e < rt ∧ rt - e = ru - j := by
  have hjl : j ≤ u.length := by have := hu.le_length; omega
  have her : e < rt := by
    by_contra hc
    have hper := (ht.periodic_iff he).mpr (by omega)
    rw [← h] at hper
    have := (hu.periodic_iff hjl).mp hper
    omega
  exact ⟨her, (PeriodicSplit.rest_length_eq hu ht hjl he h).symm⟩

/-- A target rest cut and its partner. -/
theorem partner_eq_t {u t : Word α} {ru rt : ℕ} (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit
  ξ p t rt) {s e : ℕ}
    (he : e < rt) (hs : s ≤ u.length)
    (h : prepend (t.drop e) ξ = prepend (u.drop s) ξ) : s < ru ∧ ru - s = rt - e := by
  have hel : e ≤ t.length := by have := ht.le_length; omega
  have hsr : s < ru := by
    by_contra hc
    have hper := (hu.periodic_iff hs).mpr (by omega)
    rw [← h] at hper
    have := (ht.periodic_iff hel).mp hper
    omega
  exact ⟨hsr, PeriodicSplit.rest_length_eq hu ht hs hel h.symm⟩

/-- An unpartnered rest cut cannot be extended to any suffix of the other word. -/
theorem unpartnered_ext (hp : LeastStreamPeriod ξ p) {v v' : Word α} {r j : ℕ}
    (hv : PeriodicSplit ξ p v r) (hj : j < r)
    (hun : ∀ e ≤ v'.length, prepend (v.drop j) ξ ≠ prepend (v'.drop e) ξ)
    {z : Word α} (k : ℕ) (hk : k ≤ v'.length) :
    prepend z (prepend (v.drop j) ξ) ≠ prepend (v'.drop k) ξ := by
  intro h
  rcases le_total z.length (v'.drop k).length with hl | hl
  · obtain ⟨_, h2⟩ := prepend_eq_prepend_le hl h
    rw [List.drop_drop] at h2
    exact hun _ (by simp at hl; omega) h2
  · obtain ⟨_, h2⟩ := prepend_eq_prepend_le hl h.symm
    have h3 := congrArg (fun f => fun i => f ((z.drop (v'.drop k).length).length + i)) h2
    simp only [shift_prepend_self] at h3
    have hper : StreamPeriod (prepend (v.drop j) ξ) p := by
      rw [← h3]; exact streamPeriod_shift hp.2.1 _
    have := (hv.periodic_iff (by have := hv.le_length; omega)).mp hper
    omega

end SS2

/-- Explicit polynomial capacity of the pumping argument. -/
def pumpCapacity (a b c d : ℕ) : ℕ :=
  2 * a * a * b * c * d + a * a * c + a * b * d + 2 * a * b * c * d + a * c + b * d

namespace SS2
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')
variable {ξ : ℕ → α} {p : ℕ}

/-! ## The six deletions -/

/-- Both periodic ends are long: delete a factor of both at the same depths. -/
theorem shrink_joint (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ u.length - ru)
    (h' : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ t.length - rt) :
    I.Shrinks ξ u t := by
  classical
  have hul := hu.le_length
  have htl := ht.le_length
  obtain ⟨d₁, d₂, hlt, hle, hf⟩ := exists_lt_map_eq _
    (fun d => (I.A.atCut u (u.length - d), I.A'.atCut u (u.length - d),
      I.B.atCut t (t.length - d), I.B'.atCut t (t.length - d),
      (⟨d % p, Nat.mod_lt _ hp.1⟩ : Fin p), decide (I.HeadFrom u t (u.length - d)))) le_rfl
  simp only [Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide] at hf
  obtain ⟨hfA, hfA', hfB, hfB', hfm, hfh⟩ := hf
  obtain ⟨x, w, hu', hxl, hwl⟩ := exists_split3 u (i := u.length - d₂)
    (j := u.length - d₁) (by omega) (by omega)
  obtain ⟨x', w', ht', hxl', hwl'⟩ := exists_split3 t (i := t.length - d₂)
    (j := t.length - d₁) (by omega) (by omega)
  have hyl : (u.drop (u.length - d₁)).length = d₁ := by simp; omega
  have hyl' : (t.drop (t.length - d₁)).length = d₁ := by simp; omega
  have hW : prepend w (prepend (u.drop (u.length - d₁)) ξ) =
      prepend (u.drop (u.length - d₁)) ξ := by
    rw [← prepend_assoc, ← drop_mid_eq hu', hxl]
    exact hu.cut_eq hp (by omega) (by omega) (by omega) (by omega) (by
      rw [show u.length - (u.length - d₂) = d₂ by omega,
        show u.length - (u.length - d₁) = d₁ by omega]
      exact hfm.symm)
  have hW' : prepend w' (prepend (t.drop (t.length - d₁)) ξ) =
      prepend (t.drop (t.length - d₁)) ξ := by
    rw [← prepend_assoc, ← drop_mid_eq ht', hxl']
    exact ht.cut_eq hp (by omega) (by omega) (by omega) (by omega) (by
      rw [show t.length - (t.length - d₂) = d₂ by omega,
        show t.length - (t.length - d₁) = d₁ by omega]
      exact hfm.symm)
  apply I.shrink_of_delete hu' ht' (Or.inl (List.ne_nil_of_length_pos (by omega))) hg
  · exact I.A.runFrom_of_atCut hu' hxl (by omega) hfA.symm
  · exact I.A'.runFrom_of_atCut hu' hxl (by omega) hfA'.symm
  · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB.symm
  · exact I.B'.runFrom_of_atCut ht' hxl' (by omega) hfB'.symm
  · intro s _ e _ hdep hsuf
    refine ⟨by omega, ?_⟩
    rw [prepend_mid hW, prepend_mid hW']
    exact hsuf
  · intro s _ k _ _ hsuf
    rw [prepend_mid hW]
    exact hsuf
  · intro k _ e he hdep
    exfalso
    omega
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    by_cases hH : I.HeadFrom u t (u.length - d₁)
    · obtain ⟨s, e, hs, hev⟩ := hH
      have hd := aligned_depth hev.1
      have := hev.1.1
      have := hev.1.2.1
      exact ⟨s, e, hev, Or.inl ⟨by omega, by omega⟩⟩
    · have hs₀ : s₀ < u.length - d₂ := by
        by_contra hc
        exact hH (hfh.mpr ⟨s₀, e₀, by omega, hev₀⟩)
      have hd := aligned_depth hev₀.1
      have := hev₀.1.1
      have := hev₀.1.2.1
      exact ⟨s₀, e₀, hev₀, Or.inr ⟨by omega, by omega, by omega, by omega⟩⟩

/-- The spine's periodic end is much longer: delete a factor of it alone. -/
theorem shrink_soloU (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h : t.length - rt + Fintype.card (SA × SA' × Fin p) ≤ u.length - ru) :
    I.Shrinks ξ u t := by
  have hul := hu.le_length
  have htl := ht.le_length
  have hc : 0 < Fintype.card (SA × SA' × Fin p) :=
    Fintype.card_pos_iff.mpr ⟨(I.A.start, I.A'.start, ⟨0, hp.1⟩)⟩
  obtain ⟨d₁, d₂, hlt, hle, hf⟩ := exists_lt_map_eq _
    (fun d => (I.A.atCut u (u.length - (t.length - rt + d)),
      I.A'.atCut u (u.length - (t.length - rt + d)),
      (⟨(t.length - rt + d) % p, Nat.mod_lt _ hp.1⟩ : Fin p))) le_rfl
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hf
  obtain ⟨hfA, hfA', hfm⟩ := hf
  obtain ⟨x, w, hu', hxl, hwl⟩ := exists_split3 u (i := u.length - (t.length - rt + d₂))
    (j := u.length - (t.length - rt + d₁)) (by omega) (by omega)
  have hW : prepend w (prepend (u.drop (u.length - (t.length - rt + d₁))) ξ) =
      prepend (u.drop (u.length - (t.length - rt + d₁))) ξ := by
    rw [← prepend_assoc, ← drop_mid_eq hu', hxl]
    exact hu.cut_eq hp (by omega) (by omega) (by omega) (by omega) (by
      rw [show u.length - (u.length - (t.length - rt + d₂)) = t.length - rt + d₂ by omega,
        show u.length - (u.length - (t.length - rt + d₁)) = t.length - rt + d₁ by omega]
      exact hfm.symm)
  apply I.shrink_of_delete (x' := []) (w' := []) (y' := t) hu' (by simp)
    (Or.inl (List.ne_nil_of_length_pos (by omega))) hg
  · exact I.A.runFrom_of_atCut hu' hxl (by omega) hfA.symm
  · exact I.A'.runFrom_of_atCut hu' hxl (by omega) hfA'.symm
  · rfl
  · rfl
  · intro s _ e he; simp at he
  · intro s _ k _ _ hsuf
    rw [prepend_mid hW]
    exact hsuf
  · intro k _ e he; simp at he
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    have hm := aligned_le_min hp hu ht (by omega) hev₀.1
    have := hev₀.1.1
    exact ⟨s₀, e₀, hev₀, Or.inl ⟨by omega, by simp⟩⟩

/-- The target's periodic end is much longer: delete a factor of it alone,
strictly beyond the spine's periodic end. -/
theorem shrink_soloT (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h : u.length - ru + 1 + Fintype.card (SB × SB' × Fin p) ≤ t.length - rt) :
    I.Shrinks ξ u t := by
  have hul := hu.le_length
  have htl := ht.le_length
  obtain ⟨d₁, d₂, hlt, hle, hf⟩ := exists_lt_map_eq _
    (fun d => (I.B.atCut t (t.length - (u.length - ru + 1 + d)),
      I.B'.atCut t (t.length - (u.length - ru + 1 + d)),
      (⟨(u.length - ru + 1 + d) % p, Nat.mod_lt _ hp.1⟩ : Fin p))) le_rfl
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hf
  obtain ⟨hfB, hfB', hfm⟩ := hf
  obtain ⟨x', w', ht', hxl', hwl'⟩ := exists_split3 t
    (i := t.length - (u.length - ru + 1 + d₂)) (j := t.length - (u.length - ru + 1 + d₁))
    (by omega) (by omega)
  have hyl' : (t.drop (t.length - (u.length - ru + 1 + d₁))).length =
      u.length - ru + 1 + d₁ := by simp; omega
  have hW' : prepend w' (prepend (t.drop (t.length - (u.length - ru + 1 + d₁))) ξ) =
      prepend (t.drop (t.length - (u.length - ru + 1 + d₁))) ξ := by
    rw [← prepend_assoc, ← drop_mid_eq ht', hxl']
    exact ht.cut_eq hp (by omega) (by omega) (by omega) (by omega) (by
      rw [show t.length - (t.length - (u.length - ru + 1 + d₂)) = u.length - ru + 1 + d₂ by
          omega,
        show t.length - (t.length - (u.length - ru + 1 + d₁)) = u.length - ru + 1 + d₁ by
          omega]
      exact hfm.symm)
  apply I.shrink_of_delete (x := []) (w := []) (y := u) (by simp) ht'
    (Or.inr (List.ne_nil_of_length_pos (by omega))) hg
  · rfl
  · rfl
  · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB.symm
  · exact I.B'.runFrom_of_atCut ht' hxl' (by omega) hfB'.symm
  · intro s hs; simp at hs
  · intro s hs; simp at hs
  · intro k hk e he hdep hsuf
    exfalso
    have hel : e ≤ t.length := by omega
    have hsuf' : prepend (u.drop k) ξ = prepend (t.drop e) ξ := by
      rw [hsuf, ← prepend_mid hW', ← drop_delete_left w' _ he.le, ht']
    by_cases hk' : ru ≤ k
    · omega
    · obtain ⟨her, hrl⟩ := partner_eq hu ht (by omega : k < ru) hel hsuf'
      omega
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    have hm := aligned_le_min hp hu ht (by omega) hev₀.1
    have hd := aligned_depth hev₀.1
    have := hev₀.1.1
    have := hev₀.1.2.1
    exact ⟨s₀, e₀, hev₀, Or.inl ⟨by simp, by omega⟩⟩

/-- Many partnered rest cuts: delete a factor of the common rest suffix. -/
theorem shrink_restSync (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (P : Finset ℕ)
    (hP : ∀ j ∈ P, j < ru ∧ ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ)
    (h : Fintype.card (SA × SA' × SB × SB' × Bool) < P.card) : I.Shrinks ξ u t := by
  classical
  have hul := hu.le_length
  have htl := ht.le_length
  have hpart : ∀ j ∈ P, j < ru ∧ ru - j ≤ rt ∧
      prepend (u.drop j) ξ = prepend (t.drop (rt - (ru - j))) ξ := by
    intro j hj
    obtain ⟨hjr, e, he, heq⟩ := hP j hj
    obtain ⟨her, hrl⟩ := partner_eq hu ht hjr he heq
    refine ⟨hjr, by omega, ?_⟩
    rw [show rt - (ru - j) = e by omega]
    exact heq
  obtain ⟨j₁, hj₁, j₂, hj₂, hlt, hf⟩ := exists_lt_map_eq_finset P
    (fun j => (I.A.atCut u j, I.A'.atCut u j, I.B.atCut t (rt - (ru - j)),
      I.B'.atCut t (rt - (ru - j)), decide (I.HeadFrom u t j))) h
  simp only [Prod.mk.injEq, decide_eq_decide] at hf
  obtain ⟨hfA, hfA', hfB, hfB', hfh⟩ := hf
  obtain ⟨hr₁, hle₁, hU₁⟩ := hpart j₁ hj₁
  obtain ⟨hr₂, hle₂, hU₂⟩ := hpart j₂ hj₂
  obtain ⟨x, w, hu', hxl, hwl⟩ := exists_split3 u hlt.le (by omega : j₂ ≤ u.length)
  obtain ⟨x', w', ht', hxl', hwl'⟩ := exists_split3 t (i := rt - (ru - j₁))
    (j := rt - (ru - j₂)) (by omega) (by omega)
  have hX := nonSelfSimilar_of_rest hp hu hr₂
  have hww : w = w' := by
    have h1 : prepend (w ++ u.drop j₂) ξ = prepend (w' ++ t.drop (rt - (ru - j₂))) ξ := by
      rw [← drop_mid_eq hu', ← drop_mid_eq ht', hxl, hxl']
      exact hU₁
    rw [prepend_assoc, prepend_assoc, ← hU₂] at h1
    exact ((prepend_eq_iff_of_length_eq (by omega) _ _).mp h1).1
  apply I.shrink_of_delete hu' ht' (Or.inl (List.ne_nil_of_length_pos (by omega))) hg
  · exact I.A.runFrom_of_atCut hu' hxl (by omega) hfA
  · exact I.A'.runFrom_of_atCut hu' hxl (by omega) hfA'
  · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB
  · exact I.B'.runFrom_of_atCut ht' hxl' (by omega) hfB'
  · intro s hs e he hdep hsuf
    rw [prepend_assoc, prepend_assoc, ← hU₂] at hsuf
    have h2 := hX.prepend_inj hsuf
    have h3 := congrArg List.length h2
    simp only [List.length_drop] at h3
    refine ⟨by omega, ?_⟩
    rw [prepend_assoc (x.drop s ++ w), prepend_assoc (x'.drop e ++ w'), ← hU₂, h2, hww]
  · intro s hs k hk _ hsuf
    exfalso
    rw [prepend_assoc, ← prepend_shift _ ξ hk, ← hU₂] at hsuf
    exact hX.ne_shift (List.ne_nil_of_length_pos (by simp; omega)) k hsuf
  · intro k hk e he _ hsuf
    exfalso
    rw [prepend_assoc, ← prepend_shift _ ξ hk, ← hU₂] at hsuf
    exact hX.ne_shift (List.ne_nil_of_length_pos (by simp; omega)) k hsuf.symm
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    by_cases hH : I.HeadFrom u t j₂
    · obtain ⟨s, e, hs, hev⟩ := hH
      have hsl := hev.1.1
      have hel := hev.1.2.1
      refine ⟨s, e, hev, Or.inl ⟨by omega, ?_⟩⟩
      by_contra hc
      have hee : e ≤ rt - (ru - j₂) := by omega
      have h1 : prepend (u.drop s) ξ = prepend (t.drop e) ξ := by rw [hev.1.2.2]
      have h2 : (fun i => prepend (u.drop j₂) ξ ((s - j₂) + i)) = prepend (u.drop s) ξ := by
        rw [prepend_shift _ ξ (by simp; omega), List.drop_drop, Nat.add_sub_cancel' hs]
      rw [← h2, drop_split t hee, prepend_assoc, ← hU₂] at h1
      exact hX.ne_shift (List.ne_nil_of_length_pos (by simp; omega)) _ h1.symm
    · have hs₀ : s₀ < j₁ := by
        by_contra hc
        exact hH (hfh.mp ⟨s₀, e₀, by omega, hev₀⟩)
      obtain ⟨hle, hdr⟩ := aligned_shift hev₀.1 hs₀.le (by omega)
      have hX₁ : NonSelfSimilar (prepend (t.drop (rt - (ru - j₁))) ξ) := by
        rw [← hU₁]; exact nonSelfSimilar_of_rest hp hu hr₁
      have he := cut_unique hX₁ hle (by omega) (by rw [← hdr]; exact hU₁)
      have hd := aligned_depth hev₀.1
      exact ⟨s₀, e₀, hev₀, Or.inr ⟨by omega, by omega, by omega, by omega⟩⟩

/-- Many unpartnered spine rest cuts: delete a factor of the spine alone. -/
theorem shrink_restU (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (P : Finset ℕ)
    (hP : ∀ j ∈ P, j < ru ∧ ∀ e ≤ t.length, prepend (u.drop j) ξ ≠ prepend (t.drop e) ξ)
    (h : Fintype.card (SA × SA') < P.card) : I.Shrinks ξ u t := by
  have hul := hu.le_length
  obtain ⟨i, hi, j, hj, hlt, hf⟩ := exists_lt_map_eq_finset P
    (fun j => (I.A.atCut u j, I.A'.atCut u j)) h
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hjr, hun⟩ := hP j hj
  obtain ⟨x, w, hu', hxl, hwl⟩ := exists_split3 u hlt.le (by omega : j ≤ u.length)
  apply I.shrink_of_delete (x' := []) (w' := []) (y' := t) hu' (by simp)
    (Or.inl (List.ne_nil_of_length_pos (by omega))) hg
  · exact I.A.runFrom_of_atCut hu' hxl (by omega) hf.1
  · exact I.A'.runFrom_of_atCut hu' hxl (by omega) hf.2
  · rfl
  · rfl
  · intro s _ e he; simp at he
  · intro s _ k hk _ hsuf
    exfalso
    rw [prepend_assoc] at hsuf
    exact unpartnered_ext hp hu hjr hun k hk hsuf
  · intro k _ e he; simp at he
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    have hs₀ : j ≤ s₀ := by
      by_contra hc
      obtain ⟨hle, hdr⟩ := aligned_shift hev₀.1 (by omega : s₀ ≤ j) (by omega)
      exact hun _ hle (by rw [hdr])
    exact ⟨s₀, e₀, hev₀, Or.inl ⟨by omega, by simp⟩⟩

/-- Many unpartnered target rest cuts: delete a factor of the target alone. -/
theorem shrink_restT (hp : LeastStreamPeriod ξ p) {u t : Word α} {rt : ℕ}
    (hg : I.PumpGood ξ u t) (ht : PeriodicSplit ξ p t rt) (P : Finset ℕ)
    (hP : ∀ e ∈ P, e < rt ∧ ∀ s ≤ u.length, prepend (t.drop e) ξ ≠ prepend (u.drop s) ξ)
    (h : Fintype.card (SB × SB') < P.card) : I.Shrinks ξ u t := by
  have htl := ht.le_length
  obtain ⟨i, hi, j, hj, hlt, hf⟩ := exists_lt_map_eq_finset P
    (fun e => (I.B.atCut t e, I.B'.atCut t e)) h
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hjr, hun⟩ := hP j hj
  obtain ⟨x', w', ht', hxl', hwl'⟩ := exists_split3 t hlt.le (by omega : j ≤ t.length)
  apply I.shrink_of_delete (x := []) (w := []) (y := u) (by simp) ht'
    (Or.inr (List.ne_nil_of_length_pos (by omega))) hg
  · rfl
  · rfl
  · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hf.1
  · exact I.B'.runFrom_of_atCut ht' hxl' (by omega) hf.2
  · intro s hs; simp at hs
  · intro s hs; simp at hs
  · intro k hk e _ _ hsuf
    exfalso
    rw [prepend_assoc] at hsuf
    exact unpartnered_ext hp ht hjr hun k hk hsuf.symm
  · obtain ⟨s₀, -, e₀, -, hev₀⟩ := hg.2.2.2.1
    have he₀ : j ≤ e₀ := by
      by_contra hc
      obtain ⟨hle, hdr⟩ := aligned_shift (aligned_symm hev₀.1) (by omega : e₀ ≤ j) (by omega)
      exact hun _ hle (by rw [hdr])
    exact ⟨s₀, e₀, hev₀, Or.inl ⟨by simp, by omega⟩⟩

/-! ## Pigeonhole over the six cases and the induction -/

/-- One deletion applies to every survivor-free pre-hole with a long word. -/
theorem pump_step (hp : LeastStreamPeriod ξ p) {u t : Word α} (hg : I.PumpGood ξ u t)
    (hlong : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) +
        Fintype.card (SA × SA' × Fin p) + Fintype.card (SB × SB' × Fin p) +
        Fintype.card (SA × SA' × SB × SB' × Bool) + Fintype.card (SA × SA') +
        Fintype.card (SB × SB') ≤ max u.length t.length) :
    I.Shrinks ξ u t := by
  classical
  obtain ⟨ru, hu⟩ := periodicSplit_exists hp.2.1 u
  obtain ⟨rt, ht⟩ := periodicSplit_exists hp.2.1 t
  have hul := hu.le_length
  have htl := ht.le_length
  by_cases h1 : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ u.length - ru ∧
      Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ t.length - rt
  · exact I.shrink_joint hp hg hu ht h1.1 h1.2
  by_cases h2 : t.length - rt + Fintype.card (SA × SA' × Fin p) ≤ u.length - ru
  · exact I.shrink_soloU hp hg hu ht h2
  by_cases h3 : u.length - ru + 1 + Fintype.card (SB × SB' × Fin p) ≤ t.length - rt
  · exact I.shrink_soloT hp hg hu ht h3
  set Pu := (Finset.range ru).filter
    (fun j => ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ) with hPu
  by_cases h4 : Fintype.card (SA × SA' × SB × SB' × Bool) < Pu.card
  · refine I.shrink_restSync hp hg hu ht Pu (fun j hj => ?_) h4
    simp only [hPu, Finset.mem_filter, Finset.mem_range] at hj
    exact hj
  set Uu := (Finset.range ru).filter
    (fun j => ¬ ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ) with hUu
  by_cases h5 : Fintype.card (SA × SA') < Uu.card
  · refine I.shrink_restU hp hg hu Uu (fun j hj => ?_) h5
    simp only [hUu, Finset.mem_filter, Finset.mem_range, not_exists, not_and] at hj
    exact ⟨hj.1, fun e he heq => hj.2 e he heq⟩
  set Pt := (Finset.range rt).filter
    (fun e => ∃ s ≤ u.length, prepend (t.drop e) ξ = prepend (u.drop s) ξ) with hPt
  set Ut := (Finset.range rt).filter
    (fun e => ¬ ∃ s ≤ u.length, prepend (t.drop e) ξ = prepend (u.drop s) ξ) with hUt
  by_cases h6 : Fintype.card (SB × SB') < Ut.card
  · refine I.shrink_restT hp hg ht Ut (fun e he => ?_) h6
    simp only [hUt, Finset.mem_filter, Finset.mem_range, not_exists, not_and] at he
    exact ⟨he.1, fun s hs heq => he.2 s hs heq⟩
  exfalso
  have hru : Pu.card + Uu.card = ru := by
    rw [hPu, hUu, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hrt : Pt.card + Ut.card = rt := by
    rw [hPt, hUt, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hPtu : Pt.card ≤ Pu.card := by
    apply Finset.card_le_card_of_injOn (fun e => ru - (rt - e))
    · intro e he
      simp only [Finset.mem_coe, hPt, Finset.mem_filter, Finset.mem_range] at he
      obtain ⟨her, s, hs, heq⟩ := he
      obtain ⟨hsr, hrl⟩ := partner_eq_t hu ht her hs heq
      simp only [Finset.mem_coe, hPu, Finset.mem_filter, Finset.mem_range]
      rw [show ru - (rt - e) = s by omega]
      exact ⟨hsr, e, by omega, heq.symm⟩
    · intro e₁ he₁ e₂ he₂ heq
      simp only [Finset.mem_coe, hPt, Finset.mem_filter, Finset.mem_range] at he₁ he₂
      obtain ⟨her₁, s₁, hs₁, heq₁⟩ := he₁
      obtain ⟨her₂, s₂, hs₂, heq₂⟩ := he₂
      have := partner_eq_t hu ht her₁ hs₁ heq₁
      have := partner_eq_t hu ht her₂ hs₂ heq₂
      simp only at heq
      omega
  rw [not_and_or] at h1
  omega

/-- Repeated deletion, by induction on the total length. -/
theorem pumpGood_short (hp : LeastStreamPeriod ξ p) {K : ℕ}
    (hK : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) +
        Fintype.card (SA × SA' × Fin p) + Fintype.card (SB × SB' × Fin p) +
        Fintype.card (SA × SA' × SB × SB' × Bool) + Fintype.card (SA × SA') +
        Fintype.card (SB × SB') ≤ K) :
    ∀ N, ∀ u t : Word α, u.length + t.length ≤ N → I.PumpGood ξ u t →
      ∃ u' t', I.PumpGood ξ u' t' ∧ I.A.run u' = I.A.run u ∧
        u'.length < K ∧ t'.length < K := by
  intro N
  induction N with
  | zero =>
    intro u t hN hg
    by_cases hs : u.length < K ∧ t.length < K
    · exact ⟨u, t, hg, rfl, hs⟩
    · rw [not_and_or] at hs
      obtain ⟨u', t', -, -, hlt⟩ := I.pump_step hp hg (by omega)
      omega
  | succ N ih =>
    intro u t hN hg
    by_cases hs : u.length < K ∧ t.length < K
    · exact ⟨u, t, hg, rfl, hs⟩
    · rw [not_and_or] at hs
      obtain ⟨u', t', hg', hrun, hlt⟩ := I.pump_step hp hg (by omega)
      obtain ⟨u'', t'', hg'', hrun', hl⟩ := ih u' t' (by omega) hg'
      exact ⟨u'', t'', hg'', hrun'.trans hrun, hl⟩

omit [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB'] in
/-- The six signature counts, for a period at most `N_A`. -/
theorem pumpSize_le {p : ℕ} (hpa : p ≤ Fintype.card SA) :
    Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) +
        Fintype.card (SA × SA' × Fin p) + Fintype.card (SB × SB' × Fin p) +
        Fintype.card (SA × SA' × SB × SB' × Bool) + Fintype.card (SA × SA') +
        Fintype.card (SB × SB') ≤
      pumpCapacity (Fintype.card SA) (Fintype.card SB) (Fintype.card SA')
        (Fintype.card SB') := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, pumpCapacity]
  generalize Fintype.card SA = a at hpa ⊢
  generalize Fintype.card SB = b
  generalize Fintype.card SA' = c
  generalize Fintype.card SB' = d
  nlinarith [Nat.mul_le_mul_left (2 * a * b * c * d) hpa, Nat.mul_le_mul_left (a * c) hpa,
    Nat.mul_le_mul_left (b * d) hpa]

/-- `PurelyPeriodicShortPreHole` with the polynomial capacity. Thinness is
not used; the lasso only bounds the least period by `N_A`. -/
theorem purelyPeriodicShortPreHole_pump [Inhabited α] :
    I.PurelyPeriodicShortPreHole
      (pumpCapacity (Fintype.card SA) (Fintype.card SB) (Fintype.card SA')
        (Fintype.card SB')) := by
  rintro q ξ - hl hper ⟨u, t, hph, hq, hsf⟩
  obtain ⟨p, hp⟩ := leastPeriod_exists hper
  have hpa := I.lasso_leastPeriod_le hl hp
  obtain ⟨u', t', hg, hrun, hu', ht'⟩ := I.pumpGood_short hp (pumpSize_le hpa) _ u t le_rfl
    ((I.pumpGood_iff ξ u t).mpr ⟨hph, hsf⟩)
  obtain ⟨hph', hsf'⟩ := (I.pumpGood_iff ξ u' t').mp hg
  exact ⟨u', t', hph', hrun.trans hq, hsf', hu', ht'⟩

end SS2

/-- The polynomial capacity is below the capacity `C_I`. -/
theorem pumpCapacity_le {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    pumpCapacity a b c d ≤ nonMortalPreHoleCapacity a b c d := by
  unfold nonMortalPreHoleCapacity
  refine le_trans ?_ (le_max_right _ _)
  have hbd : 1 ≤ b * d := Nat.mul_pos hb hd
  have hac : 1 ≤ a * c := Nat.mul_pos ha hc
  have hbcd : 1 ≤ b * c * d := Nat.mul_pos (Nat.mul_pos hb hc) hd
  have h8 : pumpCapacity a b c d ≤ 8 * (a * a) * (b * c * d) := by
    unfold pumpCapacity
    nlinarith [Nat.mul_le_mul_left (a * a * c) hbd, Nat.mul_le_mul_left (a * b * d) hac,
      Nat.mul_le_mul_left (b * c * d * a) ha, Nat.mul_le_mul_left (a * c) hbd,
      Nat.mul_le_mul_left (a * c * (b * d)) ha, Nat.mul_le_mul_left (b * d) hac,
      Nat.mul_le_mul_left (b * d * (a * c)) ha]
  have h2 : 2 ^ 11 ≤ 2 ^ (a * a + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : a * a ≤ a ^ 3 := by
    rw [pow_succ, pow_two]; exact Nat.le_mul_of_pos_right _ ha
  calc pumpCapacity a b c d ≤ 8 * (a * a) * (b * c * d) := h8
    _ ≤ 2 ^ 11 * (a * a) * (b * c * d) := by gcongr; norm_num
    _ ≤ 2 ^ (a * a + 11) * a ^ 3 * (b * c * d) := by gcongr
    _ = 2 ^ (a * a + 11) * a ^ 3 * b * c * d := by ring

/-- The open periodic premise of `NonMortalBound`, discharged with the
capacity. -/
theorem purelyPeriodicShortPreHole_capacity [Inhabited α] (a b c d : ℕ)
    (I : SS2 α (Fin a) (Fin b) (Fin c) (Fin d)) :
    I.PurelyPeriodicShortPreHole (nonMortalPreHoleCapacity a b c d) := by
  have h := I.purelyPeriodicShortPreHole_pump
  simp only [Fintype.card_fin] at h
  have hle := pumpCapacity_le (Fin.pos I.A.start) (Fin.pos I.B.start)
    (Fin.pos I.A'.start) (Fin.pos I.B'.start)
  intro q ξ hq hl hper hex
  obtain ⟨u, t, h1, h2, h3, h4, h5⟩ := h q ξ hq hl hper hex
  exact ⟨u, t, h1, h2, h3, h4.trans_le hle, h5.trans_le hle⟩

/-- The unconditional non-mortal short-hole bound,
with the existing bound `nonMortalHoleBound`. -/
theorem nonMortalShortHoleBound_pump [Fintype α] [DecidableEq α] [Inhabited α] :
  NonMortalShortHoleBound α nonMortalHoleBound :=
  nonMortalShortHoleBound_of_periodic purelyPeriodicShortPreHole_capacity

/-- A polynomial hole bound, from the pumping capacity. -/
def pumpHoleBound : HoleBound := fun a b c d =>
  4 * max (12 * a * b * c * d) (pumpCapacity a b c d) + 6 * a

/-- The non-mortal short-hole bound with the polynomial bound `pumpHoleBound`. -/
theorem nonMortalShortHoleBound_poly [Fintype α] [DecidableEq α] [Inhabited α] :
  NonMortalShortHoleBound α pumpHoleBound := by
  intro a b c d I _ hcase
  obtain ⟨u, t, hp, hb | ⟨hthin, ξ, hs, hf⟩⟩ := hcase
  · obtain ⟨v, w, hv, hlen⟩ := I.short_branching_hole hp hb
    refine ⟨v, w, hv, ?_⟩
    simp only [Fintype.card_fin] at hlen
    have hK := le_max_left (12 * a * b * c * d) (pumpCapacity a b c d)
    change v.length + w.length ≤ 4 * max _ _ + 6 * a
    omega
  · have hl := I.thin_lasso hthin hs
    by_cases hper : ∃ p, 0 < p ∧ StreamPeriod ξ p
    · obtain ⟨v, w, hp, he, hf, hv, hw⟩ :=
        I.purelyPeriodicShortPreHole_pump (I.A.run u) ξ hthin hl hper ⟨u, t, hp, rfl, hf⟩
      simp only [Fintype.card_fin] at hv hw
      have hK := le_max_right (12 * a * b * c * d) (pumpCapacity a b c d)
      obtain ⟨v', w', hh, hlen⟩ := I.short_hole_of_lasso hp (he ▸ hl) hf
        (hv.trans_le hK) (hw.trans_le hK)
      refine ⟨v', w', hh, ?_⟩
      simp only [Fintype.card_fin] at hlen
      change v'.length + w'.length ≤ 4 * max _ _ + 6 * a
      omega
    · obtain ⟨v, w, hv, hlen⟩ := I.short_aperiodic_hole hp hl hper
      refine ⟨v, w, hv, ?_⟩
      simp only [Fintype.card_fin] at hlen
      have hK := le_max_left (12 * a * b * c * d) (pumpCapacity a b c d)
      change v.length + w.length ≤ 4 * max _ _ + 6 * a
      omega

/-- The polynomial bound is never worse than the earlier one. -/
theorem pumpHoleBound_le (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    pumpHoleBound a b c d ≤ nonMortalHoleBound a b c d := by
  have := pumpCapacity_le ha hb hc hd
  unfold pumpHoleBound nonMortalHoleBound nonMortalPreHoleCapacity at *
  have := le_max_left (12 * a * b * c * d) (2 ^ (a * a + 11) * a ^ 3 * b * c * d)
  omega

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
  · rw [SS2.safeFrom_iff]
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

/-- The pumping theorem on this family; the capacity is `pumpCapacity 3 1 1 2 = 68`. -/
theorem periodicGuard_long_short (k : ℕ) :
    ∃ u t, periodicGuardInstance.IsPreHole u t ∧ periodicGuardInstance.A.run u = 1 ∧
      periodicGuardInstance.SurvivorFree u t (fun _ => false) ∧ u.length < 68 ∧
      t.length < 68 := by
  obtain ⟨hph, hsf⟩ := (periodicGuardInstance.pumpGood_iff _ _ _).mp (periodicGuard_long k)
  have hrun : periodicGuardInstance.A.run (true :: List.replicate k false) = 1 := by
    have := periodicGuard_atCut k (k + 1) (by omega)
    rwa [LDFA.atCut, List.take_of_length_le (by simp)] at this
  have h := periodicGuardInstance.purelyPeriodicShortPreHole_pump 1 (fun _ => false)
    periodicGuard_thin periodicGuard_lasso ⟨1, by decide, fun _ => rfl⟩
    ⟨_, _, hph, hrun, hsf⟩
  simpa [pumpCapacity] using h

/-- All initial letters enter state one; only letter one then stays safe. -/
def ternaryPumpInstance : SS2 (Fin 3) (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
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
  · rw [SS2.safeFrom_iff]
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

/-- The generic induction shortens the ternary family and keeps its endpoint. -/
theorem ternaryPump_long_short (k : ℕ) :
    ∃ u t, ternaryPumpInstance.IsPreHole u t ∧ ternaryPumpInstance.A.run u = 1 ∧
      ternaryPumpInstance.SurvivorFree u t (fun _ => 1) ∧
      u.length < 68 ∧ t.length < 68 := by
  have hp : LeastStreamPeriod (fun _ => (1 : Fin 3)) 1 :=
    ⟨by decide, fun _ => rfl, fun _ hq _ => hq⟩
  have hsize := SS2.pumpSize_le (SA := Fin 3) (SB := Fin 1)
    (SA' := Fin 1) (SB' := Fin 2) (p := 1) (by decide)
  obtain ⟨u, t, hg, hrun, hu, ht⟩ := ternaryPumpInstance.pumpGood_short hp hsize _ _ _
    le_rfl (ternaryPump_long k)
  obtain ⟨hph, hsf⟩ := (ternaryPumpInstance.pumpGood_iff _ _ _).mp hg
  have hend : ternaryPumpInstance.A.run (2 :: List.replicate k 1) = 1 := by
    have h := ternaryPump_atCut k (k + 1) (by omega)
    rwa [LDFA.atCut, List.take_of_length_le (by simp)] at h
  exact ⟨u, t, hph, hrun.trans hend, hsf,
    by simpa [pumpCapacity] using hu, by simpa [pumpCapacity] using ht⟩

/-- Exercise the final polynomial bound on the ternary periodic trigger. -/
theorem ternary_periodic_short_hole_poly :
    ∃ u t, ternaryThinInstance.IsHole u t ∧ u.length + t.length ≤ 204 := by
  obtain ⟨hfh, hthin, hl, _, u, t, hp, hq, hf⟩ := ternary_periodic_trigger
  apply nonMortalShortHoleBound_poly 2 1 1 2 ternaryThinInstance hfh
  refine ⟨u, t, hp, Or.inr ⟨hq ▸ hthin, _, ?_, hf⟩⟩
  exact hq ▸ ternaryThinInstance.lasso_safe hl

end NonMortalExamples


end DeciENSSE.Core
