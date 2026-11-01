import DeciENSSE.Core.Words.NonMortalLasso

/-! # Periodic splits and forbidden suffix pairs

Periodic suffixes characterize surviving comparisons and their forbidden guard pairs.

## Main declarations

- `PeriodicSplit`
- `periodicSplit_exists`
- `SS2.survivorFree_iff_periodic_tests`
-/

namespace DeciENSSE.Core

variable {α : Type*}

/-- A fixed finite prefix of a periodic stream is exactly a prefix whose
length is a period. This includes the empty word. -/
theorem prepend_fixed_iff_prefix_period {ξ : ℕ → α} (w : Word α) :
    prepend w ξ = ξ ↔ StreamPrefix w ξ ∧ StreamPeriod ξ w.length := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [StreamPrefix, ← h, prepend_prefix]
    · intro i
      have hh := congrFun h (i + w.length)
      simpa [prepend] using hh.symm
  · rintro ⟨hw, hp⟩
    funext i
    by_cases hi : i < w.length
    · simpa [prepend, hi] using streamPrefix_iff.mp hw i hi
    · have hh := hp (i - w.length)
      simpa [prepend, hi, Nat.sub_add_cancel (by omega : w.length ≤ i)] using hh.symm

/-- Least-period form of the finite fixed-prefix criterion. -/
theorem prepend_fixed_iff_prefix_dvd {ξ : ℕ → α} {p : ℕ}
    (hp : LeastStreamPeriod ξ p) (w : Word α) :
    prepend w ξ = ξ ↔ StreamPrefix w ξ ∧ p ∣ w.length := by
  rw [prepend_fixed_iff_prefix_period]
  by_cases hw : w.length = 0
  · simp [hw, StreamPeriod]
  · rw [leastPeriod_dvd_iff hp (by omega)]

/-- Removing a finite prefix from a prefixed stream. -/
theorem prepend_shift (w : Word α) (ξ : ℕ → α) {n : ℕ} (hn : n ≤ w.length) :
    (fun i => prepend w ξ (n + i)) = prepend (w.drop n) ξ := by
  funext i
  by_cases hi : n + i < w.length
  · simp [prepend, hi, show i < w.length - n by omega, List.getElem_drop]
  · simp [prepend, hi, show ¬ i < w.length - n by omega,
      show n + i - w.length = i - (w.length - n) by omega]

/-- Shifting a purely periodic stream loses no information. -/
theorem periodic_shift_injective {ξ η : ℕ → α} {p : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hη : StreamPeriod η p) (n : ℕ)
    (he : (fun i => ξ (n + i)) = (fun i => η (n + i))) : ξ = η := by
  funext i
  have hlarge : n ≤ i + n * p := by nlinarith
  have hh := congrFun he (i + n * p - n)
  simp only [Nat.add_sub_of_le hlarge] at hh
  rw [streamPeriod_mod hξ, streamPeriod_mod hη] at hh
  simpa only [Nat.add_mul_mod_self_right, ← streamPeriod_mod hξ,
    ← streamPeriod_mod hη] using hh

/-- A periodic finite extension has the same least period as its tail. -/
theorem leastPeriod_prepend {ξ : ℕ → α} {p : ℕ}
    (hp : LeastStreamPeriod ξ p) {w : Word α}
    (hw : StreamPeriod (prepend w ξ) p) : LeastStreamPeriod (prepend w ξ) p := by
  refine ⟨hp.1, hw, ?_⟩
  intro q hq hper
  apply hp.2.2 q hq
  simpa [prepend] using streamPeriod_shift hper w.length

/-- Equality of two periodic ends is exactly equality of their depth residues.
 -/
theorem periodic_ends_eq_iff {ξ : ℕ → α} {p : ℕ}
    (hp : LeastStreamPeriod ξ p) {u t : Word α}
    (hu : StreamPeriod (prepend u ξ) p) (ht : StreamPeriod (prepend t ξ) p) :
    prepend u ξ = prepend t ξ ↔ u.length % p = t.length % p := by
  constructor
  · intro he
    apply (leastPeriod_suffix_eq_iff (leastPeriod_prepend hp hu) u.length t.length).mp
    have hx : (fun i => prepend u ξ (u.length + i)) = ξ := by
      funext i; simp [prepend]
    have hy : (fun i => prepend u ξ (t.length + i)) = ξ := by
      rw [he]; funext i; simp [prepend]
    exact hx.trans hy.symm
  · intro he
    apply periodic_shift_injective hp.1 hu ht (u.length + t.length)
    have hh := (leastPeriod_suffix_eq_iff hp t.length u.length).mpr he.symm
    funext i
    have hi := congrFun hh i
    simpa [prepend, show ¬ u.length + t.length + i < u.length by omega,
      show ¬ u.length + t.length + i < t.length by omega,
      show u.length + t.length + i - u.length = t.length + i by omega,
      show u.length + t.length + i - t.length = u.length + i by omega] using hi

/-- Splitting an equality of infinite words at equally long finite prefixes. -/
theorem prepend_eq_iff_of_length_eq {u t : Word α} (hlen : u.length = t.length)
    (ξ η : ℕ → α) :
    prepend u ξ = prepend t η ↔ u = t ∧ ξ = η := by
  constructor
  · intro h
    have hw := congrArg (fun f => streamPrefix f u.length) h
    rw [prepend_prefix, hlen, prepend_prefix] at hw
    subst t
    exact ⟨rfl, prepend_injective u h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A cut splitting a word into its rest and maximal periodic end. Periodicity
of the infinite suffix is an algebraic description of membership in
`Suf(η*)`; no choice of a power of the period is needed. -/
structure PeriodicSplit (ξ : ℕ → α) (p : ℕ) (w : Word α) (r : ℕ) : Prop where
  le_length : r ≤ w.length
  periodic : StreamPeriod (prepend (w.drop r) ξ) p
  minimal : ∀ s < r, ¬ StreamPeriod (prepend (w.drop s) ξ) p

/-- Every word has a maximal periodic end. -/
theorem periodicSplit_exists {ξ : ℕ → α} {p : ℕ}
    (hp : StreamPeriod ξ p) (w : Word α) : ∃ r, PeriodicSplit ξ p w r := by
  classical
  have h : ∃ r, StreamPeriod (prepend (w.drop r) ξ) p :=
    ⟨w.length, by simpa using hp⟩
  exact ⟨Nat.find h, Nat.find_min' h (by simpa using hp), Nat.find_spec h,
    fun s hs => Nat.find_min h hs⟩

namespace PeriodicSplit

variable {ξ : ℕ → α} {p : ℕ} {w : Word α} {r : ℕ}

/-- Precisely the cuts in the periodic end have
periodic infinite suffixes. -/
theorem periodic_iff (h : PeriodicSplit ξ p w r) {s : ℕ} (hs : s ≤ w.length) :
    StreamPeriod (prepend (w.drop s) ξ) p ↔ r ≤ s := by
  constructor
  · intro hp
    by_contra hn
    exact h.minimal s (by omega) hp
  · intro hrs
    have hh := streamPeriod_shift h.periodic (s - r)
    rw [prepend_shift _ _ (by simp; omega), List.drop_drop,
      Nat.add_sub_of_le hrs] at hh
    exact hh

/-- Uniqueness makes the semantic split independent of a chosen witness. -/
theorem unique (h : PeriodicSplit ξ p w r) {s : ℕ} (hs : PeriodicSplit ξ p w s) :
    r = s := by
  have h₁ := (h.periodic_iff hs.le_length).mp hs.periodic
  have h₂ := (hs.periodic_iff h.le_length).mp h.periodic
  omega

/-- Equal infinite suffixes have the same number of remaining rest letters.
This includes the mixed periodic/rest case: their remaining rest lengths
are respectively zero and positive, so they cannot be equal. -/
theorem rest_length_eq {u t : Word α} {ru rt s e : ℕ}
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (hs : s ≤ u.length) (he : e ≤ t.length)
    (heq : prepend (u.drop s) ξ = prepend (t.drop e) ξ) : ru - s = rt - e := by
  have hle : ∀ {u t : Word α} {ru rt s e : ℕ},
      PeriodicSplit ξ p u ru → PeriodicSplit ξ p t rt →
      s ≤ u.length → e ≤ t.length →
      prepend (u.drop s) ξ = prepend (t.drop e) ξ → ru - s ≤ rt - e := by
    intro u t ru rt s e hu ht hs he heq
    by_contra hn
    have hsmall : s + (rt - e) < ru := by omega
    have hsuf := congrArg (fun f : ℕ → α => fun i => f (rt - e + i)) heq
    rw [prepend_shift _ _ (by simp; have := hu.le_length; omega),
      prepend_shift _ _ (by simp; have := ht.le_length; omega),
      List.drop_drop, List.drop_drop] at hsuf
    have hper := (ht.periodic_iff (s := e + (rt - e)) (by have := ht.le_length; omega)).mpr
      (by omega)
    rw [← hsuf] at hper
    exact hu.minimal _ hsmall hper
  exact Nat.le_antisymm (hle hu ht hs he heq) (hle ht hu he hs heq.symm)

/-- Suffix equality, with the common-rest suffix expressed by its
letters rather than the numerical length of the longest common suffix.
The two alternatives are exactly the periodic and rest cases. -/
theorem suffix_eq_iff {u t : Word α} {ru rt s e : ℕ}
    (hp : LeastStreamPeriod ξ p)
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (hs : s ≤ u.length) (he : e ≤ t.length) :
    prepend (u.drop s) ξ = prepend (t.drop e) ξ ↔
      (ru ≤ s ∧ rt ≤ e ∧ (u.length - s) % p = (t.length - e) % p) ∨
      (s < ru ∧ e < rt ∧ ru - s = rt - e ∧
        (u.drop s).take (ru - s) = (t.drop e).take (rt - e) ∧
        (u.length - ru) % p = (t.length - rt) % p) := by
  have split (w : Word α) (s r : ℕ) (hsr : s ≤ r) :
      w.drop s = (w.drop s).take (r - s) ++ w.drop r := by
    simpa [List.drop_drop, Nat.add_sub_of_le hsr] using
      (List.take_append_drop (r - s) (w.drop s)).symm
  have restCase (hsr : s < ru) (her : e < rt) (hlen : ru - s = rt - e) :
      (prepend (u.drop s) ξ = prepend (t.drop e) ξ) ↔
        (u.drop s).take (ru - s) = (t.drop e).take (rt - e) ∧
          (u.length - ru) % p = (t.length - rt) % p := by
    have hcore : ((u.drop s).take (ru - s)).length =
        ((t.drop e).take (rt - e)).length := by
      simp only [List.length_take, List.length_drop]
      have := hu.le_length
      have := ht.le_length
      omega
    conv_lhs =>
      rw [split u s ru (by omega), split t e rt (by omega), prepend_assoc, prepend_assoc]
    rw [prepend_eq_iff_of_length_eq hcore,
      periodic_ends_eq_iff hp hu.periodic ht.periodic]
    simp only [List.length_drop]
  constructor
  · intro h
    have hrest := rest_length_eq hu ht hs he h
    by_cases hsr : ru ≤ s
    · have her : rt ≤ e := by omega
      exact Or.inl ⟨hsr, her, by
        simpa only [List.length_drop] using
          (periodic_ends_eq_iff hp ((hu.periodic_iff hs).mpr hsr)
            ((ht.periodic_iff he).mpr her)).mp h⟩
    · have hsr' : s < ru := by omega
      have her : e < rt := by omega
      exact Or.inr ⟨hsr', her, hrest, (restCase hsr' her hrest).mp h⟩
  · rintro (⟨hsr, her, hmod⟩ | ⟨hsr, her, hlen, hcore⟩)
    · exact (periodic_ends_eq_iff hp ((hu.periodic_iff hs).mpr hsr)
        ((ht.periodic_iff he).mpr her)).mpr (by simpa using hmod)
    · exact (restCase hsr her hlen).mpr hcore

/-- Beyond the shorter periodic end,
equal suffixes are possible only when the two periodic-end lengths agree;
then equality is precisely equality of the corresponding rest suffixes. -/
theorem aligned_suffix_eq_iff {u t : Word α} {ru rt k : ℕ}
    (hp : LeastStreamPeriod ξ p) (hu : PeriodicSplit ξ p u ru)
    (ht : PeriodicSplit ξ p t rt) (hku : k ≤ u.length) (hkt : k ≤ t.length) :
    u.drop (u.length - k) = t.drop (t.length - k) ↔
      k ≤ min (u.length - ru) (t.length - rt) ∨
      (u.length - ru = t.length - rt ∧ u.length - ru < k ∧
        (u.drop (u.length - k)).take (k - (u.length - ru)) =
          (t.drop (t.length - k)).take (k - (t.length - rt))) := by
  have hs : u.length - k ≤ u.length := Nat.sub_le _ _
  have he : t.length - k ≤ t.length := Nat.sub_le _ _
  have hlen : (u.drop (u.length - k)).length = (t.drop (t.length - k)).length := by
    simp [Nat.sub_sub_self hku, Nat.sub_sub_self hkt]
  have heq := prepend_eq_iff_of_length_eq hlen ξ ξ
  simp only [and_true] at heq
  rw [← heq, suffix_eq_iff hp hu ht hs he]
  have hul := hu.le_length
  have htl := ht.le_length
  have hau : ru - (u.length - k) = k - (u.length - ru) := by omega
  have hat : rt - (t.length - k) = k - (t.length - rt) := by omega
  simp only [Nat.sub_sub_self hku, Nat.sub_sub_self hkt, hau, hat, and_true]
  constructor
  · rintro (⟨hsr, her⟩ | ⟨hsr, her, hdist, hcore, _⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega, hcore⟩
  · rintro (h | ⟨hlen, hk, hc⟩)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega, by omega, hc, by rw [hlen]⟩

end PeriodicSplit

/-- A finite test for a periodic extension, assuming its infinite tail is
already periodic. It makes the semantic periodic-end test executable. -/
theorem prepend_period_iff_finite {ξ : ℕ → α} {p : ℕ}
    (hp : StreamPeriod ξ p) (w : Word α) :
    StreamPeriod (prepend w ξ) p ↔
      ∀ i < w.length, prepend w ξ (i + p) = prepend w ξ i := by
  constructor
  · exact fun h i _ => h i
  · intro h i
    by_cases hi : i < w.length
    · exact h i hi
    · have hh := hp (i - w.length)
      simpa [prepend, hi, show ¬ i + p < w.length by omega,
        show i + p - w.length = i - w.length + p by omega] using hh

/-- The first letter before a maximal periodic end must fail this test. -/
theorem prepend_letter_period_iff {ξ : ℕ → α} {p : ℕ}
    (hp : 0 < p) (hξ : StreamPeriod ξ p) (c : α) :
    StreamPeriod (prepend [c] ξ) p ↔ c = ξ (p - 1) := by
  rw [prepend_period_iff_finite hξ]
  simp [prepend, show p ≠ 0 by omega, eq_comm]

namespace SS2

/-- Survival after cancellation of the common finite target suffix.
Unlike the nonaligned formulation, this also covers zero offset. -/
theorem survives_iff_overhang_fixed [Inhabited α] {u t : Word α} {s e : ℕ}
    (hc : Cross u t s e) (ξ : ℕ → α) :
    Survives u t s e ξ ↔ prepend (overhang u t s e) ξ = ξ := by
  have hlen := hc.2.2.length_le
  simp only [List.length_drop] at hlen
  have he := survives_iff_prepend_eq hc.1 hc.2.1 hlen ξ
  rw [and_iff_right hc, cross_factor hc, prepend_assoc] at he
  exact he.trans ⟨fun h => prepend_injective (t.drop e) h,
    congrArg (prepend (t.drop e))⟩

/-- The residue test alone is insufficient: the overhang must also be a
prefix of the fixed periodic stream. -/
theorem survives_iff_periodic_prefix [Inhabited α] {u t : Word α} {s e : ℕ}
    (hc : Cross u t s e) {ξ : ℕ → α} {p : ℕ}
    (hp : LeastStreamPeriod ξ p) :
    Survives u t s e ξ ↔
      StreamPrefix (overhang u t s e) ξ ∧ offset u t s e % p = 0 := by
  rw [survives_iff_overhang_fixed hc, prepend_fixed_iff_prefix_dvd hp,
    overhang_length, Nat.dvd_iff_mod_eq_zero]

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-- The residue dimension in Appendix C.6 is at most the spine-state count,
even if the supplied lasso presentation has a nonempty transient part. -/
theorem lasso_leastPeriod_le [Inhabited α] {q : SA} {ξ : ℕ → α} {p : ℕ}
    (hl : I.Lasso q ξ) (hp : LeastStreamPeriod ξ p) : p ≤ Fintype.card SA := by
  obtain ⟨α₀, l, hn, hlen, _, _, rfl⟩ := hl
  have hs := leastPeriod_suffix hp α₀.length
  have hper : StreamPeriod (fun i => prepend α₀ (periodicStream l) (α₀.length + i))
      l.length := by
    simpa [prepend] using periodicStream_period l
  have hle := hs.2.2 l.length (List.length_pos_iff.mpr hn) hper
  omega

/-- Event-freedom as the universal infinite-suffix guard test. The target's
first rejection at its last cut is essential here. -/
theorem survivorFree_iff_suffix_guard [Inhabited α] {u t : Word α} {ξ : ℕ → α}
    (hj : I.J t = some t.length) :
    I.SurvivorFree u t ξ ↔
      ∀ s ≤ u.length, ∀ e ≤ t.length, t.length - e ≤ u.length - s →
        prepend (u.drop s) ξ = prepend (t.drop e) ξ →
        (I.A.atCut u s, I.B.atCut t e) ∉ I.Guard := by
  constructor
  · intro hf s hs e he hlen heq hg
    obtain ⟨hc, hsurv⟩ := (survives_iff_prepend_eq hs he hlen ξ).mpr heq
    exact hf s e ⟨hc, ⟨t.length, by simp [hj], he⟩, hg⟩ hsurv
  · intro hf s e hev hsurv
    have hlen := hev.1.2.2.length_le
    simp only [List.length_drop] at hlen
    exact hf s hev.1.1 e hev.1.2.1 hlen
      ((survives_iff_prepend_eq hev.1.1 hev.1.2.1 hlen ξ).mp ⟨hev.1, hsurv⟩)
      hev.2.2

/-- The inverse image of a target state under the guard relation. -/
def periodicGuardInverse (b : SB) : Finset SA :=
  Finset.univ.filter (fun a => (a, b) ∈ I.Guard)

/-- Membership in a guard inverse is the corresponding guard-pair condition. -/
@[simp] theorem mem_periodicGuardInverse (a : SA) (b : SB) :
    a ∈ I.periodicGuardInverse b ↔ (a, b) ∈ I.Guard := by
  simp [periodicGuardInverse]

/-- Add a reached target cut to its residue's forbidden-state set. -/
def periodicInsert {p : ℕ} (F : Fin p → Finset SA) (i : Fin p) (b : SB) :
    Fin p → Finset SA :=
  Function.update F i (F i ∪ I.periodicGuardInverse b)

/-- Insertion adds the target state at its periodic residue. -/
@[simp] theorem mem_periodicInsert {p : ℕ} (F : Fin p → Finset SA)
    (i j : Fin p) (a : SA) (b : SB) :
    a ∈ I.periodicInsert F i b j ↔ a ∈ F j ∨ (j = i ∧ (a, b) ∈ I.Guard) := by
  by_cases h : j = i
  · subst j; simp [periodicInsert]
  · simp [periodicInsert, h]

/-- The sets only grow; insert-before-test includes the current aligned pair. -/
theorem periodicInsert_mono {p : ℕ} (F : Fin p → Finset SA) (i j : Fin p) (b : SB) :
    F j ⊆ I.periodicInsert F i b j := by
  intro a ha
  exact (I.mem_periodicInsert F i j a b).mpr (Or.inl ha)

/-- Semantic forbidden sets after the target cuts of depths `0,...,k`
have been visited. In uses below `k` does not exceed the target length. -/
def periodicForbidden {p : ℕ} (t : Word α) (k : ℕ) (i : Fin p) : Finset SA :=
  Finset.univ.filter (fun a => ∃ d ≤ k, d % p = i.val ∧
    (a, I.B.atCut t (t.length - d)) ∈ I.Guard)

/-- Forbidden membership records a guarded periodic comparison at an earlier cut. -/
@[simp] theorem mem_periodicForbidden {p : ℕ} (t : Word α) (k : ℕ) (i : Fin p) (a : SA) :
    a ∈ I.periodicForbidden t k i ↔
      ∃ d ≤ k, d % p = i.val ∧ (a, I.B.atCut t (t.length - d)) ∈ I.Guard := by
  simp [periodicForbidden]

/-- Initialization includes the depth-zero target cut. -/
theorem periodicForbidden_zero {p : ℕ} (t : Word α) :
    I.periodicForbidden (p := p) t 0 =
      (fun i => if i.val = 0 then I.periodicGuardInverse (I.B.run t) else ∅) := by
  funext i
  apply Finset.ext
  intro a
  by_cases hi : i.val = 0 <;>
    simp [hi, periodicForbidden, periodicGuardInverse, LDFA.atCut, eq_comm]

/-- Exact recursive update; the new target cut is added before the guard test. -/
theorem periodicForbidden_succ {p : ℕ} (hp : 0 < p) (t : Word α) (k : ℕ) :
    I.periodicForbidden t (k + 1) =
      I.periodicInsert (I.periodicForbidden t k) ⟨(k + 1) % p, Nat.mod_lt _ hp⟩
        (I.B.atCut t (t.length - (k + 1))) := by
  funext i
  apply Finset.ext
  intro a
  rw [mem_periodicForbidden, mem_periodicInsert, mem_periodicForbidden]
  constructor
  · rintro ⟨d, hd, hm, hg⟩
    by_cases hdk : d ≤ k
    · exact Or.inl ⟨d, hdk, hm, hg⟩
    · have he : d = k + 1 := by omega
      subst d
      exact Or.inr ⟨Fin.ext hm.symm, hg⟩
  · rintro (⟨d, hd, hm, hg⟩ | ⟨rfl, hg⟩)
    · exact ⟨d, by omega, hm, hg⟩
    · exact ⟨k + 1, le_rfl, rfl, hg⟩

/-- The forbidden-set test expresses both residue agreement and the
nonnegative signed offset. Target cuts deeper than the current spine cut
must not enter this test. -/
theorem periodicForbidden_test_iff {p : ℕ} (hp : 0 < p) (u t : Word α)
    {ru rt : ℕ} (hu : ru ≤ u.length) (ht : rt ≤ t.length) :
    (∀ k ≤ u.length - ru,
      I.A.atCut u (u.length - k) ∉
        I.periodicForbidden t (min k (t.length - rt)) ⟨k % p, Nat.mod_lt _ hp⟩) ↔
    (∀ s ≤ u.length, ∀ e ≤ t.length, ru ≤ s → rt ≤ e →
      t.length - e ≤ u.length - s → (u.length - s) % p = (t.length - e) % p →
      (I.A.atCut u s, I.B.atCut t e) ∉ I.Guard) := by
  constructor
  · intro h s hs e he hrs hre hlen hmod hg
    apply h (u.length - s) (by omega)
    rw [mem_periodicForbidden]
    refine ⟨t.length - e, by omega, hmod.symm, ?_⟩
    simpa only [Nat.sub_sub_self hs, Nat.sub_sub_self he] using hg
  · intro h k hk hf
    obtain ⟨d, hd, hmod, hg⟩ := (I.mem_periodicForbidden _ _ _ _).mp hf
    have hdl : d ≤ t.length := by omega
    have hkl : k ≤ u.length := by omega
    exact h (u.length - k) (by omega) (t.length - d) (by omega)
      (by omega) (by omega) (by omega)
      (by simpa only [Nat.sub_sub_self hkl, Nat.sub_sub_self hdl] using hmod.symm) hg

/-- Exact semantic guard tests: residue-indexed forbidden sets handle
periodic ends, and equal remaining rest words handle cuts in the rest. -/
theorem survivorFree_iff_periodic_tests [Inhabited α] {u t : Word α} {ξ : ℕ → α} {p ru rt : ℕ}
    (hp : LeastStreamPeriod ξ p) (hu : PeriodicSplit ξ p u ru)
    (ht : PeriodicSplit ξ p t rt) (hj : I.J t = some t.length) :
    I.SurvivorFree u t ξ ↔
      (∀ k ≤ u.length - ru,
        I.A.atCut u (u.length - k) ∉ I.periodicForbidden t (min k (t.length - rt))
          ⟨k % p, Nat.mod_lt _ hp.1⟩) ∧
      ((t.length - rt ≤ u.length - ru ∧
          (u.length - ru) % p = (t.length - rt) % p) →
        ∀ k, 0 < k → k ≤ ru → k ≤ rt →
          (u.drop (ru - k)).take k = (t.drop (rt - k)).take k →
          (I.A.atCut u (ru - k), I.B.atCut t (rt - k)) ∉ I.Guard) := by
  rw [I.survivorFree_iff_suffix_guard hj,
    I.periodicForbidden_test_iff hp.1 u t hu.le_length ht.le_length]
  have hul := hu.le_length
  have htl := ht.le_length
  constructor
  · intro h
    constructor
    · intro s hs e he hrs hre hlen hmod
      apply h s hs e he hlen
      exact (PeriodicSplit.suffix_eq_iff hp hu ht hs he).mpr
        (Or.inl ⟨hrs, hre, hmod⟩)
    · rintro ⟨hlen, hmod⟩ k hk hku hkt hcore
      have hs : ru - k ≤ u.length := by omega
      have he : rt - k ≤ t.length := by omega
      apply h (ru - k) hs (rt - k) he (by omega)
      apply (PeriodicSplit.suffix_eq_iff hp hu ht hs he).mpr
      exact Or.inr ⟨by omega, by omega, by omega,
        by simpa only [Nat.sub_sub_self hku, Nat.sub_sub_self hkt] using hcore, hmod⟩
  · rintro ⟨hper, hrest⟩ s hs e he hlen heq
    rcases (PeriodicSplit.suffix_eq_iff hp hu ht hs he).mp heq with
      ⟨hrs, hre, hmod⟩ | ⟨hrs, hre, hdist, hcore, hmod⟩
    · exact hper s hs e he hrs hre hlen hmod
    · have hle : t.length - rt ≤ u.length - ru := by omega
      have h := hrest ⟨hle, hmod⟩ (ru - s) (by omega) (by omega) (by omega)
      have hs' : ru - (ru - s) = s := by omega
      have he' : rt - (ru - s) = e := by omega
      rw [hs', he'] at h
      apply h
      simpa only [hdist] using hcore

end SS2

namespace NonMortalExamples

/-- Both first letters enter a thin zero-loop. The guard at the initial
spine state distinguishes the overhangs `[false]` and `[true]`. -/
def periodicGuardDFA : LDFA Bool (Fin 3) :=
  ⟨0, fun q c => if q = 0 ∨ (q = 1 ∧ c = false) then 1 else 2⟩

/-- A thin instance whose initial guard distinguishes the two overhang letters. -/
def periodicGuardInstance : SS2 Bool (Fin 3) (Fin 1) (Fin 1) (Fin 2) :=
  { CoreExamples.smallInstance periodicGuardDFA {2} with Guard := {(0, 0)} }

/-- The concrete starting state is thin. -/
theorem periodicGuard_thin : periodicGuardInstance.Thin 1 := by
  exact @of_decide_eq_true _ (periodicGuardInstance.thinDecidable 1) (by decide +kernel)

/-- The concrete safe stream has a bounded lasso representation. -/
theorem periodicGuard_lasso : periodicGuardInstance.Lasso 1 (fun _ => false) := by
  refine ⟨[], [false], by decide, by decide, by decide, rfl, ?_⟩
  funext i
  simp [prepend, periodicStream, Nat.mod_one]

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem periodicGuard_preHoles :
    periodicGuardInstance.IsPreHole [false] [] ∧
      periodicGuardInstance.IsPreHole [true] [] := by decide +kernel

/-- A zero residue is not by itself sufficient for survival. -/
theorem periodicGuard_true_survivorFree :
    periodicGuardInstance.SurvivorFree [true] [] (fun _ => false) := by
  rw [periodicGuardInstance.survivorFree_iff_suffix_guard (by decide)]
  intro s hs e he _ heq
  have he' : e = 0 := by simpa using he
  subst e
  have hs' : s ≤ 1 := by simpa using hs
  interval_cases s
  · have hh := congrFun heq 0
    simp [prepend] at hh
  · decide +kernel

/-- The zero overhang event survives the constant-zero stream. -/
theorem periodicGuard_false_survivor :
    periodicGuardInstance.Event [false] [] 0 0 ∧
      SS2.Survives [false] [] 0 0 (fun _ => false) := by
  refine ⟨by unfold SS2.Event SS2.Cross; decide +kernel, ?_⟩
  apply (SS2.survives_iff_overhang_fixed (by simp [SS2.Cross] : SS2.Cross [false] [] 0 0) _).mpr
  funext i
  simp [SS2.overhang, prepend]

/-- Maximal periodic ends have witnesses even when the rest is nonempty. -/
theorem periodicSplit_nonempty_rest :
    PeriodicSplit (fun _ => false) 1 [true, false, false] 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        simp [prepend, show ¬ i + 1 + 1 < 2 by omega,
          show ¬ i + 1 + 1 + 1 < 2 by omega]
  · intro s hs h
    have hs' : s = 0 := by omega
    subst s
    have hh := h 0
    simp [prepend] at hh

/-- A third letter can form the nonperiodic rest before a constant tail. -/
theorem periodicSplit_ternary_rest :
    PeriodicSplit (fun _ => (0 : Fin 3)) 1 [2, 0, 0] 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        simp [prepend, show ¬ i + 1 + 1 < 2 by omega,
          show ¬ i + 1 + 1 + 1 < 2 by omega]
  · intro s hs h
    have hs' : s = 0 := by omega
    subst s
    have hh := h 0
    simp [prepend] at hh

/-- The guard at depth zero is included, even at zero offset. -/
theorem periodicForbidden_aligned :
    (0 : Fin 3) ∈ periodicGuardInstance.periodicForbidden [] 0 (0 : Fin 1) := by
  decide +kernel

/-- A deeper target cut enters its own residue only when it is reached. -/
theorem periodicForbidden_depth_cutoff :
    periodicGuardInstance.periodicForbidden [false] 0 (1 : Fin 2) = ∅ ∧
      periodicGuardInstance.periodicForbidden [false] 1 (1 : Fin 2) = {0} := by
  decide +kernel

/-- The surviving false overhang is rejected by the semantic periodic test. -/
theorem periodicGuard_false_forbidden :
    ¬ (∀ k ≤ ([false] : Word Bool).length,
      periodicGuardInstance.A.atCut [false] (1 - k) ∉
        periodicGuardInstance.periodicForbidden [] (min k 0) (0 : Fin 1)) := by
  intro h
  exact h 1 (by decide) (by decide +kernel)

end NonMortalExamples


end DeciENSSE.Core
