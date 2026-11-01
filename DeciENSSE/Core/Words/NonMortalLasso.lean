import Mathlib.Tactic.Linarith
import DeciENSSE.Core.Words.NonMortal

/-! # Periods and finite lasso enumeration

Least periods control lasso survivors and give a finite enumeration of safe lassos.

## Main declarations

- `leastPeriod_suffix`
- `SS2.lasso_breaking_prefix`
- `SS2.lassoPairs`
- `SS2.thin_lassos_finite`
-/

namespace DeciENSSE.Core

variable {α : Type*}

/-- Cancel a finite common prefix from an infinite-word equation. -/
theorem prepend_factor {x y : Word α} {ξ : ℕ → α} (hl : y.length ≤ x.length)
    (he : prepend x ξ = prepend y ξ) :
    ∃ r, x = y ++ r ∧ prepend r ξ = ξ := by
  have hx : StreamPrefix x (prepend x ξ) := prepend_prefix x ξ
  have hy : StreamPrefix y (prepend x ξ) := by rw [he]; exact prepend_prefix y ξ
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

namespace SS2
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-- The overhang is also the final suffix of the spine of length equal to the offset. -/
theorem overhang_suffix {u t : Word α} {s e : ℕ} (hc : Cross u t s e) :
    overhang u t s e = u.drop (u.length - offset u t s e) := by
  have hlen := hc.2.2.length_le
  simp only [List.length_drop] at hlen
  unfold overhang offset
  rw [List.drop_drop]
  congr 1
  have hs := hc.1
  omega

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

omit [Inhabited α] in
/-- The lasso breaking window is bounded by the word lengths and state count. -/
theorem lasso_breaking_length_le {u t : Word α} {s e : ℕ} (hc : Cross u t s e) (α₀ l : Word α) :
    α₀.length + l.length + offset u t s e - 1 ≤ α₀.length + l.length + u.length - 1 := by
  have := cross_offset_le hc
  omega

/-- A uniform finite prefix of a survivor-free lasso completes a pre-hole. -/
theorem lasso_completes {u t : Word α} {ξ : ℕ → α} (hlasso : I.Lasso (I.A.run u) ξ)
    (hf : I.SurvivorFree u t ξ) :
    I.Completes u t (streamPrefix ξ (u.length + Fintype.card SA - 1)) := by
  refine ⟨I.infiniteSafe_prefix (I.lasso_safe hlasso) _, ?_⟩
  obtain ⟨α₀, l, hl, hlen, _, _, rfl⟩ := hlasso
  intro s e he hk
  have hbreak := lasso_breaking_prefix he.1 α₀ l hl (hf s e he)
  apply hbreak
  apply keeps_prefix hk
  apply streamPrefix_prefix
  have := cross_offset_le he.1
  omega

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

/-- Executable state-kind tests, def:nm-kinds. -/
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


omit [Fintype α] [DecidableEq α] [Inhabited α] in
/-- Graph characterization of viability from def:nm-kinds. -/
theorem viable_iff_reachable_cyclic (q : SA) :
    I.Viable q ↔ ∃ r, I.SafeReachable q r ∧ I.Cyclic r := by
  constructor
  · intro hv
    obtain ⟨ξ, hξ⟩ := (I.viable_iff q).mp hv
    let w := streamPrefix ξ (Fintype.card SA)
    have hw : I.SafeFrom q w := I.infiniteSafe_prefix hξ _
    obtain ⟨i, j, hij, hj, he⟩ := I.path_repeat (q := q) (w := w) (by simp [w])
    exact ⟨I.A.runFrom q (w.take i),
      ⟨w.take i, I.safeFrom_prefix hw (List.take_prefix _ _), rfl⟩,
      I.cyclic_of_repeat hw hij hj he⟩
  · rintro ⟨r, hr, hc⟩
    exact I.viable_of_reachable hr (I.cyclic_viable hc)

omit [Fintype α] [DecidableEq α] [Inhabited α] in
/-- A nonbad state is mortal exactly when it cannot safely reach a cycle. -/
theorem mortal_iff_no_reachable_cycle (q : SA) :
    I.Mortal q ↔ q ∉ I.Bad ∧ ¬ ∃ r, I.SafeReachable q r ∧ I.Cyclic r := by
  rw [Mortal, I.viable_iff_reachable_cyclic]

omit [Fintype α] [DecidableEq α] [Inhabited α] in
/-- A factorization at the first rejected cut gives a pre-hole and its completion. -/
theorem preHole_at_rejection {u t u₀ t₀ θ : Word α} (hf : I.FH) (hh : I.IsHole u t)
    (hj : I.J t = some t₀.length) (hu : u = u₀ ++ θ) (ht : t = t₀ ++ θ) :
    I.IsPreHole u₀ t₀ ∧ I.Completes u₀ t₀ θ := by
  obtain ⟨v, w, z, hv, hw, _, hp, hc⟩ := I.hole_decomposition hf hh
  have hj' : I.J t = some w.length := by rw [hw]; exact I.J_append hp.2.1 z
  have hlen : t₀.length = w.length := Option.some.inj (hj.symm.trans hj')
  have ht₀ : t₀ = w := by
    have h := congrArg (List.take t₀.length) (ht.symm.trans hw)
    simpa [hlen] using h
  have hz : θ = z := by
    have h := ht.symm.trans hw
    rw [ht₀, List.append_cancel_left_eq] at h
    exact h
  have hu₀ : u₀ = v := by
    have h := hu.symm.trans hv
    rw [hz, List.append_cancel_right_eq] at h
    exact h
  simpa [ht₀, hu₀, hz] using And.intro hp hc

end SS2

namespace NonMortalExamples

/-- A safe zero-loop with the other letter entering a bad sink. -/
def thinDFA : LDFA Bool (Fin 2) := ⟨0, fun q c => if q = 0 ∧ c = false then 0 else 1⟩

/-- A two-state thin instance with a zero-loop and a bad sink. -/
def thinInstance : SS2 Bool (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance thinDFA {1}

/-- The concrete starting state is thin. -/
theorem thin_state : thinInstance.Thin 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro hm
    apply hm.2
    refine ⟨{0}, by simp, ?_⟩
    intro r hr
    have hr' : r = 0 := Finset.mem_singleton.mp hr
    subst r
    exact ⟨by decide, false, by decide⟩
  · rintro ⟨_, r, _, _, a, b, hab, ha, hb⟩
    have hletter (c : Bool) (hc : thinInstance.A.step r c ∉ thinInstance.Bad) :
        c = false := by
      cases c with
      | false => rfl
      | true => simp [thinInstance, CoreExamples.smallInstance, thinDFA] at hc
    exact hab ((hletter a ha).trans (hletter b hb).symm)

/-- The concrete word pair satisfies the pre-hole conditions. -/
theorem thin_preHole : thinInstance.IsPreHole [] [] := by decide +kernel

/-- The concrete safe stream has a bounded lasso representation. -/
theorem thin_lasso : thinInstance.Lasso 0 (periodicStream [false]) := by
  refine ⟨[], [false], by decide, by decide, by decide, rfl, ?_⟩
  simp

/-- The concrete continuation is survivor-free. -/
theorem thin_survivorFree : thinInstance.SurvivorFree [] [] (periodicStream [false]) := by
  intro s e he
  exact (Finset.notMem_empty _ he.2.2).elim

/-- The thin instance satisfies the non-mortal case. -/
theorem thin_case : thinInstance.FH ∧ thinInstance.NonMortalCase := by
  refine ⟨CoreExamples.smallInstance_fh _ _, [], [], thin_preHole, Or.inr ?_⟩
  exact ⟨thin_state, periodicStream [false], thinInstance.lasso_safe thin_lasso, thin_survivorFree⟩

/-- The finite lasso enumeration contains a safe lasso. -/
theorem thin_enumeration_nonempty : (thinInstance.lassoPairs 0).Nonempty := by decide +kernel

/-- An empty completion cannot remove the pending event in this instance. -/
theorem completes_nonempty : thinInstance.Completes [] [] [] := by
  refine ⟨by decide, ?_⟩
  intro s e he
  exact (Finset.notMem_empty _ he.2.2).elim

/-- A least stream period is positive. -/
theorem leastPeriod_nonempty : LeastStreamPeriod (fun _ => false) 1 := by
  exact ⟨by decide, fun _ => rfl, fun q hq _ => hq⟩

/-- The executable branching test finds the two safe nonzero ternary letters. -/
theorem ternary_branching_decide :
    @decide _ (CoreExamples.ternaryBranch.branchingDecidable 0) = true := by
  decide +kernel

/-- A single safe state over the unary alphabet. -/
def unaryInstance : SS2 (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 2) :=
  CoreExamples.smallInstance CoreExamples.oneDFA ∅

/-- The concrete starting state is thin. -/
theorem unary_thin : unaryInstance.Thin 0 := by
  exact @of_decide_eq_true _ (unaryInstance.thinDecidable 0) (by decide +kernel)

/-- The finite enumeration contains exactly the presentation of `0^ω`. -/
theorem unary_lassoPairs : unaryInstance.lassoPairs 0 = {([], [0])} := by
  decide +kernel

/-- The only safe unary stream is the constant stream. -/
theorem unary_safe_iff (ξ : ℕ → Fin 1) :
    unaryInstance.InfiniteSafe 0 ξ ↔ ξ = periodicStream [0] := by
  rw [unaryInstance.thin_lassoPairs_iff unary_thin, unary_lassoPairs]
  simp

end NonMortalExamples


end DeciENSSE.Core
