import Mathlib.Tactic.GCongr
import DeciENSSE.Core.Words.Periodic
import DeciENSSE.Core.Words.NonMortalBound

/-! # Deletion toolkit for periodic pre-holes

Deleting factors between matching reader states preserves safety, rejection,
a head witness, and survivor freeness. Periodic suffix comparisons identify cuts
that can be deleted; `Self.Pump` applies these tools in the four deletions of
the paper (`lem:nm-four`).

## Main declarations

- `TwoWordInstance.pumpGood_delete`: preserve the pre-hole pumping invariant
  (`lem:nm-deletion`).
- `TwoWordInstance.partner_eq`, `TwoWordInstance.partner_eq_t`: locate matching cuts.
- `TwoWordInstance.periodicEnd_lt`: the periodic end of a target is shorter than
  `|SB| p` (`lem:nm-target-end`).
- `pumpBound`, `pumpCapacity`, `pumpBound_le_capacity`: the pump bound
  `2aba'b' + aa'p + bp + aa' + bb'` and its value `Pcap` at `p ≤ a`.
- `pumpHoleBound`: the polynomial non-mortal bound `Lnm`.
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

variable {α : Type*}

/-! ## Infinite words that are not proper self-extensions -/

/-- No nonempty finite word extends `X` to itself. -/
def NonSelfSimilar (X : ℕ → α) : Prop := ∀ z : Word α, z ≠ [] → prepend z X ≠ X

/-- A stream is reconstructed from a prefix and the remaining suffix. -/
theorem prepend_streamPrefix_shift (X : ℕ → α) (k : ℕ) :
    prepend (streamPrefix X k) (fun i => X (k + i)) = X := by
  funext i
  by_cases hi : i < k
  · simp [prepend, hi, streamPrefix]
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

/-- A cut past an appended prefix starts its run at the prefix endpoint. -/
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

namespace TwoWordInstance
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')

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

/-- Some head pair has its spine cut at `c` or later. -/
def HeadFrom (u t : Word α) (c : ℕ) : Prop := ∃ s e, c ≤ s ∧ I.HeadEvent u t s e

end TwoWordInstance

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

namespace TwoWordInstance

/-! ## Structure of suffix-equal cut pairs -/

/-- Moving aligned cuts by the same distance preserves alignment. -/
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

end TwoWordInstance

/-- The bound of the pump (`thm:nm-pump`) for state counts `a, b, c, d` of
`A, B, A', B'` (the paper's `a, b, a', b'`) and least period `p`:
`N₁ + N₂ + N₃ + N₄ + b p` with `N₁ = a c p`, `N₂ = 2 a b c d`, `N₃ = a c`,
`N₄ = b d`. -/
def pumpBound (a b c d p : ℕ) : ℕ :=
  2 * a * b * c * d + a * c * p + b * p + a * c + b * d

/-- The capacity `Pcap(a, b, a', b') = 2aba'b' + a²a' + ab + aa' + bb'` of the
pump, its bound at the period `p = a` (`thm:nm-pump`). -/
def pumpCapacity (a b c d : ℕ) : ℕ :=
  2 * a * b * c * d + a * a * c + a * b + a * c + b * d

/-- A period at most the spine state count gives the capacity `Pcap`. -/
theorem pumpBound_le_capacity {a b c d p : ℕ} (hpa : p ≤ a) :
    pumpBound a b c d p ≤ pumpCapacity a b c d := by
  unfold pumpBound pumpCapacity
  have h1 : a * c * p ≤ a * a * c := by
    rw [show a * a * c = a * c * a by ring]; exact Nat.mul_le_mul_left _ hpa
  have h2 : b * p ≤ a * b := by
    rw [Nat.mul_comm a b]; exact Nat.mul_le_mul_left _ hpa
  omega

/-- The pump bound as the sum of the four signature counts of `lem:nm-four`
and `|SB| p`. -/
theorem pumpBound_card (SA SB SA' SB' : Type*) [Fintype SA] [Fintype SB] [Fintype SA']
    [Fintype SB'] (p : ℕ) :
    pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p =
      Fintype.card (SA × SA' × Fin p) + Fintype.card (SA × SA' × SB × SB' × Bool) +
        Fintype.card (SA × SA') + Fintype.card (SB × SB') + Fintype.card SB * p := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, pumpBound]
  ring

namespace TwoWordInstance
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')
variable {ξ : ℕ → α} {p : ℕ}

/-- **Periodic target end** (`lem:nm-target-end`). A target rejected exactly at
its end has a periodic end shorter than `|SB| p`: two periodic cuts with the
same target state and end distances congruent modulo `p` are followed by the
same letters up to the end, so the earlier one would reach the rejected
endpoint state before the end. -/
theorem periodicEnd_lt (hp : LeastStreamPeriod ξ p) {t : Word α} {rt : ℕ}
    (ht : PeriodicSplit ξ p t rt) (hopen : I.TargetOpen t) (hrej : I.B.run t ∈ I.Rej) :
    t.length - rt < Fintype.card SB * p := by
  have htl := ht.le_length
  by_contra hc
  obtain ⟨d₁, d₂, hlt, hle, hf⟩ := exists_lt_map_eq (t.length - rt)
    (fun d => (I.B.atCut t (t.length - d), (⟨d % p, Nat.mod_lt _ hp.1⟩ : Fin p)))
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
  simp only [Prod.mk.injEq, Fin.mk.injEq] at hf
  obtain ⟨hfB, hfm⟩ := hf
  obtain ⟨i, hi⟩ : ∃ i, i = t.length - d₂ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = t.length - d₁ := ⟨_, rfl⟩
  rw [← hi, ← hj] at hfB
  have heq : prepend (t.drop i) ξ = prepend (t.drop j) ξ := by
    subst hi hj
    exact ht.cut_eq hp (by omega) (by omega) (by omega) (by omega) (by
      rw [show t.length - (t.length - d₂) = d₂ by omega,
        show t.length - (t.length - d₁) = d₁ by omega]
      exact hfm.symm)
  have hjl : (t.drop j).length = d₁ := by simp; omega
  obtain ⟨hpre, -⟩ := prepend_eq_prepend_le (by simp; omega) heq.symm
  rw [hjl] at hpre
  have hcut : I.B.atCut t (i + d₁) = I.B.run t := by
    calc I.B.atCut t (i + d₁)
        = I.B.runFrom (I.B.atCut t i) ((t.drop i).take d₁) := by
          rw [LDFA.atCut, List.take_add, LDFA.run_append]; rfl
      _ = I.B.runFrom (I.B.atCut t j) (t.drop j) := by rw [← hpre, hfB]
      _ = I.B.run t := by
          rw [LDFA.atCut, ← LDFA.run_append, List.take_append_drop]
  exact hopen (i + d₁) (by omega) (hcut ▸ hrej)

end TwoWordInstance

/-- A polynomial hole bound, from the pumping capacity: the paper's
`Lnm(a, b, a', b') = 4 max(12aba'b', Pcap(a, b, a', b')) + 6a`. -/
def pumpHoleBound : HoleBound := fun a b c d =>
  4 * max (12 * a * b * c * d) (pumpCapacity a b c d) + 6 * a

end DeciENSSE.Core.Words
