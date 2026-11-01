import Mathlib.Tactic.Linarith
import DeciENSSE.Core.Words.NonMortal

/-! # Periods and finite lasso enumeration

Least periods control lasso survivors and give a finite enumeration of safe lassos.

## Main declarations

- `leastPeriod_suffix`
- `TwoWordInstance.lasso_breaking_prefix`
- `TwoWordInstance.lassoPairs`
- `TwoWordInstance.thin_lassos_finite`
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

variable {α : Type*}

/-- Cancel a finite common prefix from an infinite-word equation. -/
theorem prepend_factor {x y : Word α} {ξ : ℕ → α} (hl : y.length ≤ x.length)
    (he : prepend x ξ = prepend y ξ) :
    ∃ r, x = y ++ r ∧ prepend r ξ = ξ := by
  have hx : IsStreamPrefix x (prepend x ξ) := prepend_prefix x ξ
  have hy : IsStreamPrefix y (prepend x ξ) := by rw [he]; exact prepend_prefix y ξ
  obtain ⟨r, hr⟩ := streamPrefix_compare hy hx hl
  refine ⟨r, hr.symm, ?_⟩
  rw [← hr, prepend_assoc] at he
  exact prepend_injective y he

/-- Minimal positive period of an infinite word. -/
def LeastStreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop :=
  0 < p ∧ StreamPeriod ξ p ∧ ∀ q, 0 < q → StreamPeriod ξ q → p ≤ q

/-- A suffix of a periodic word has no new periods. -/
theorem period_of_suffix {ξ : ℕ → α} {p q k : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hq : StreamPeriod (fun i => ξ (k + i)) q) :
    StreamPeriod ξ q := by
  intro i
  have hlarge : k ≤ i + k * p := by nlinarith
  have hh := hq (i + k * p - k)
  change ξ (k + (i + k * p - k + q)) = ξ (k + (i + k * p - k)) at hh
  have he₁ : k + (i + k * p - k + q) = i + q + k * p := by omega
  have he₂ : k + (i + k * p - k) = i + k * p := by omega
  rw [he₁, he₂, streamPeriod_mod hξ (i + q + k * p),
    streamPeriod_mod hξ (i + k * p)] at hh
  simpa only [Nat.add_mul_mod_self_right, ← streamPeriod_mod hξ] using hh

/-- Every suffix has the same least period. -/
theorem leastPeriod_suffix {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p) (k : ℕ) :
    LeastStreamPeriod (fun i => ξ (k + i)) p := by
  refine ⟨hp.1, streamPeriod_shift hp.2.1 k, ?_⟩
  intro q hq hper
  exact hp.2.2 q hq (period_of_suffix hp.1 hp.2.1 hper)

/-- Periods are precisely the positive multiples of the least period. -/
theorem leastPeriod_dvd_iff {ξ : ℕ → α} {p q : ℕ} (hp : LeastStreamPeriod ξ p)
    (_hq : 0 < q) : StreamPeriod ξ q ↔ p ∣ q := by
  constructor
  · intro hper
    have hg := streamPeriod_gcd hp.2.1 hper
    have hgp := Nat.gcd_pos_of_pos_left q hp.1
    have hmin := hp.2.2 (Nat.gcd p q) hgp hg
    have hle := Nat.gcd_le_left q hp.1
    have he : Nat.gcd p q = p := by omega
    rw [← he]; exact Nat.gcd_dvd_right p q
  · intro hd i
    rw [streamPeriod_mod hp.2.1 (i + q), streamPeriod_mod hp.2.1 i]
    congr 1
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]

/-- Periods identify exactly equal suffixes modulo the least period. -/
theorem leastPeriod_suffix_eq_iff {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p)
    (i j : ℕ) : (fun n => ξ (i + n)) = (fun n => ξ (j + n)) ↔ i % p = j % p := by
  constructor
  · intro he
    wlog hij : i ≤ j generalizing i j
    · exact (this j i he.symm (by omega)).symm
    by_cases hij' : i = j
    · simp [hij']
    · have hper : StreamPeriod (fun n => ξ (i + n)) (j - i) := by
        intro n
        change ξ (i + (n + (j - i))) = ξ (i + n)
        rw [show i + (n + (j - i)) = j + n by omega]
        exact (congrFun he n).symm
      have hd := (leastPeriod_dvd_iff (leastPeriod_suffix hp i) (by omega)).mp hper
      have hj : j = i + (j - i) := by omega
      rw [hj, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod]
  · intro he
    funext n
    rw [streamPeriod_mod hp.2.1 (i + n), streamPeriod_mod hp.2.1 (j + n)]
    congr 1
    simp [Nat.add_mod, he]

/-- Every stream with a positive period has a least positive period. -/
theorem leastPeriod_exists {ξ : ℕ → α} (h : ∃ p, 0 < p ∧ StreamPeriod ξ p) :
    ∃ p, LeastStreamPeriod ξ p := by
  classical
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    fun q hq hp => Nat.find_min' h ⟨hq, hp⟩⟩

namespace TwoWordInstance
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')

variable [Inhabited α]

/-- Survival is equality of the prepended streams with nonnegative offset. -/
theorem survives_iff_prepend_eq {u t : Word α} {s e : ℕ} (hs : s ≤ u.length)
    (he : e ≤ t.length) (hl : t.length - e ≤ u.length - s) (ξ : ℕ → α) :
    (Cross u t s e ∧ Survives u t s e ξ) ↔
      prepend (u.drop s) ξ = prepend (t.drop e) ξ := by
  constructor
  · rintro ⟨hc, hsurv⟩
    rw [cross_factor hc, prepend_assoc]
    by_cases ho : overhang u t s e = []
    · simp [ho]
    · have hn : ¬ Aligned u t s e := fun h => ho ((cross_aligned_iff hc).mp h)
      have hξ := (survives_iff_periodic hc hn ξ).mp hsurv
      rw [hξ, periodicStream_fixed ho]
  · intro hh
    obtain ⟨r, hr, hfix⟩ := prepend_factor (by simpa using hl) hh
    have hc : Cross u t s e := ⟨hs, he, ⟨r, hr.symm⟩⟩
    refine ⟨hc, ?_⟩
    have hor : overhang u t s e = r := by
      unfold overhang
      rw [hr]
      simp
    by_cases hn : r = []
    · apply aligned_survives ((cross_aligned_iff hc).mpr (hor.trans hn))
    · apply (survives_iff_periodic hc (fun ha => hn (hor.symm.trans ((cross_aligned_iff hc).mp
      ha))) ξ).mpr
      rw [hor]
      exact (prepend_fixed_iff hn).mp hfix

/-- A finite window detects whether a lasso breaks a comparison. -/
theorem lasso_breaking_prefix {u t : Word α} {s e : ℕ} (hc : Cross u t s e)
    (α₀ l : Word α) (hl : l ≠ []) (hn : ¬ Survives u t s e (prepend α₀ (periodicStream l))) :
    ¬ Keeps u t s e
      (streamPrefix (prepend α₀ (periodicStream l)) (α₀.length + l.length + offset u t s e - 1))
        := by
  have ha : ¬ Aligned u t s e := fun h => hn (aligned_survives h _)
  have ho : overhang u t s e ≠ [] := fun h => ha ((cross_aligned_iff hc).mpr h)
  intro hk
  have hp := (periodic_prefix_iff ho).mp hk
  have heq : prepend α₀ (periodicStream l) = periodicStream (overhang u t s e) := by
    apply ultimately_periodic_agreement (a := α₀.length) (b := 0)
      (List.length_pos_iff.mpr hl) (List.length_pos_iff.mpr ho)
      (by simpa [prepend] using periodicStream_period l)
      (by simpa using periodicStream_period (overhang u t s e))
    intro i hi
    have hh := streamPrefix_iff.mp hp i (by simp [overhang_length] at hi ⊢; exact hi)
    simpa only [streamPrefix, List.getElem_ofFn] using hh
  exact hn ((survives_iff_periodic hc ha _).mpr heq)

/-- Every aperiodic continuation is survivor-free for a pre-hole. -/
theorem aperiodic_survivorFree {u t : Word α} (hp : I.IsPreHole u t) {ξ : ℕ → α}
    (hn : ¬ ∃ p, 0 < p ∧ StreamPeriod ξ p) : I.SurvivorFree u t ξ := by
  intro s e he hsurv
  have ha : ¬ Aligned u t s e := by
    intro h
    exact hp.2.2.2 s (Finset.mem_range.mpr (by have := he.1.1; omega))
      e (Finset.mem_range.mpr (by have := he.1.2.1; omega)) ⟨he, h⟩
  have ho : overhang u t s e ≠ [] := fun h => ha ((cross_aligned_iff he.1).mpr h)
  have hξ := (survives_iff_periodic he.1 ha ξ).mp hsurv
  exact hn ⟨(overhang u t s e).length, List.length_pos_iff.mpr ho,
    hξ ▸ periodicStream_period (overhang u t s e)⟩

variable [Fintype α] [DecidableEq α]

/-- Computable finite set of bounded safe lasso presentations at a state. -/
def lassoPairs (q : SA) : Finset (Word α × Word α) :=
  ((wordsUpTo (Fintype.card SA)).product (wordsUpTo (Fintype.card SA))).filter
    (fun p => p.2 ≠ [] ∧ p.1.length + p.2.length ≤ Fintype.card SA ∧
      I.SafeFrom q (p.1 ++ p.2) ∧ I.A.runFrom q (p.1 ++ p.2) = I.A.runFrom q p.1)

omit [Inhabited α] in
/-- Membership in the finite enumeration is the bounded safe-lasso condition. -/
theorem mem_lassoPairs (q : SA) (α₀ l : Word α) : (α₀, l) ∈ I.lassoPairs q ↔
    l ≠ [] ∧ α₀.length + l.length ≤ Fintype.card SA ∧
      I.SafeFrom q (α₀ ++ l) ∧ I.A.runFrom q (α₀ ++ l) = I.A.runFrom q α₀ := by
  rw [lassoPairs, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩ <;> rw [mem_wordsUpTo] <;> dsimp only <;> omega

/-- Enumerating `lassoPairs` enumerates exactly all infinite safe words at a thin state. -/
theorem thin_lassoPairs_iff {q : SA} (hq : I.Thin q) (ξ : ℕ → α) :
    I.InfiniteSafe q ξ ↔ ∃ p ∈ I.lassoPairs q, ξ = prepend p.1 (periodicStream p.2) := by
  rw [I.thin_lasso_iff hq]
  constructor
  · rintro ⟨α₀, l, hn, hl, hs, he, hξ⟩
    exact ⟨(α₀, l), (I.mem_lassoPairs q α₀ l).mpr ⟨hn, hl, hs, he⟩, hξ⟩
  · rintro ⟨⟨α₀, l⟩, hp, hξ⟩
    obtain ⟨hn, hl, hs, he⟩ := (I.mem_lassoPairs q α₀ l).mp hp
    exact ⟨α₀, l, hn, hl, hs, he, hξ⟩

/-- Only finitely many bounded lassos occur at a thin state. -/
theorem thin_lassos_finite {q : SA} (hq : I.Thin q) : {ξ | I.InfiniteSafe q ξ}.Finite := by
  have hf := (I.lassoPairs q).finite_toSet.image (fun p => prepend p.1 (periodicStream p.2))
  apply hf.subset
  intro ξ hξ
  obtain ⟨p, hp, he⟩ := (I.thin_lassoPairs_iff hq ξ).mp hξ
  exact ⟨p, hp, he.symm⟩

/-- Bounded search for safe reachability. -/
def safeReachableDecidable (q r : SA) : Decidable (I.SafeReachable q r) := by
  letI : Decidable (∃ w : Word α, w ∈ wordsUpTo (Fintype.card SA) ∧
      I.SafeFrom q w ∧ I.A.runFrom q w = r) :=
    Finset.decidableExistsAndFinset (s := wordsUpTo (Fintype.card SA))
      (p := fun w : Word α => I.SafeFrom q w ∧ I.A.runFrom q w = r)
  exact decidable_of_iff (∃ w : Word α, w ∈ wordsUpTo (Fintype.card SA) ∧
      I.SafeFrom q w ∧ I.A.runFrom q w = r)
    (by
      constructor
      · rintro ⟨w, _, hw, he⟩; exact ⟨w, hw, he⟩
      · intro hr
        obtain ⟨w, hw, he, hl⟩ := I.short_safeReachable hr
        exact ⟨w, (mem_wordsUpTo _ _).mpr (by omega), hw, he⟩)

/-- Bounded search for a nonempty safe cycle. -/
def cyclicDecidable (q : SA) : Decidable (I.Cyclic q) := by
  letI : Decidable (∃ w : Word α, w ∈ wordsUpTo (Fintype.card SA) ∧
      w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q) :=
    Finset.decidableExistsAndFinset (s := wordsUpTo (Fintype.card SA))
      (p := fun w : Word α => w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q)
  exact decidable_of_iff (∃ w : Word α, w ∈ wordsUpTo (Fintype.card SA) ∧
      w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q)
    (by
      constructor
      · rintro ⟨w, _, hn, hw, he⟩; exact ⟨w, hn, hw, he⟩
      · intro hc
        obtain ⟨w, hn, hw, he, hl⟩ := I.short_cyclic hc
        exact ⟨w, (mem_wordsUpTo _ _).mpr hl, hn, hw, he⟩)

/-- Decide `Branching` using finite safe reachability and cycle tests. -/
def branchingDecidable (q : SA) : Decidable (I.Branching q) := by
  letI := I.safeReachableDecidable q
  letI := I.cyclicDecidable
  unfold Branching
  infer_instance

/-- Thinness is decidable from the finite safe-state graph. -/
def thinDecidable (q : SA) : Decidable (I.Thin q) := by
  letI := I.branchingDecidable q
  unfold Thin
  infer_instance

end TwoWordInstance

end DeciENSSE.Core.Words
