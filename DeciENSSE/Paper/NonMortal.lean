import DeciENSSE.Core.Words.Self.PaperFacts

/-! # Paper contract: Non-Mortal Holes

Contract entries for the section *Non-Mortal Holes* (`sec:nm`) and its appendix (`app:nm`):
thin states, survival, lasso completion, infinite periodic words, the pre-hole graph, good
pairs, rests and periodic ends, non-self-similar words, the continuation identity, the
decomposition at the first rejected cut, the breaker, short pre-holes, aperiodic lassos, the
deletion and counting lemmas, the pump, and the three cases with the bound `Lnm`.

Streams are functions on natural numbers; `PeriodicSplit` records the rest boundary.
Completion and survivor-freeness each have a cross and a self component.
-/
namespace DeciENSSE.Paper
open Core.Words Core.Words.TwoWordInstance Core.Words.Self DeciNSSE.RejectedTail
variable {α : Type*} {SA SB SA' SB' : Type*}
variable [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
variable [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
variable (I : SelfTwoWordInstance α SA SB SA' SB')
variable {ξ : ℕ → α} {p : ℕ}

/-- **Lemma (Thin states)**, `lem:nm-thin`(1).
Form: Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_thin_1 {q : SA} {w : Word α} (hq : I.Mortal q) (hw : I.SafeFrom q w) :
    w.length < Fintype.card SA ∧ I.Mortal (I.A.runFrom q w) := by
  exact I.toTwoWordInstance.mortal_safe_word hq hw

/-- **Lemma (Thin states)**, `lem:nm-thin`(2).
Form: Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_thin_2 {q r : SA} (hq : I.Thin q) (hr : I.SafeReachable q r)
    (hc : I.Cyclic r) : ∃ c, I.A.step r c ∉ I.Bad ∧ I.Cyclic (I.A.step r c) ∧
      ∀ d, I.A.step r d ∉ I.Bad → d = c := by
  exact I.toTwoWordInstance.thin_cyclic_letter hq hr hc

/-- **Lemma (Thin states)**, `lem:nm-thin`(4).
Form: Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_thin_4 {q : SA} {w : Word α} (hq : I.Thin q)
    (hw : I.SafeFrom q w) (hm : I.Mortal (I.A.runFrom q w)) :
    w.length < Fintype.card SA := by
  exact I.toTwoWordInstance.thin_mortal_endpoint_short hq hw hm

/-- **Lemma (Survival)**, `lem:nm-survival`(2).
Form: Self comparisons are the specialization u = t and s < e. The alphabet need not be finite.
-/
theorem lem_nm_survival_2 {u t : Word α} {s e : ℕ} (hs : s ≤ u.length)
    (he : e ≤ t.length) (hl : t.length - e ≤ u.length - s) (ξ : ℕ → α) :
    (Cross u t s e ∧ Survives u t s e ξ) ↔
      prepend (u.drop s) ξ = prepend (t.drop e) ξ := by
  let : Inhabited α := ⟨ξ 0⟩
  exact survives_iff_prepend_eq hs he hl ξ

/-- **Lemma (Survival)**, `lem:nm-survival`(3).
Form: The overhang length is offset; self comparisons are the specialization u = t and s < e. A default alphabet letter presents periodic streams; its value is irrelevant for nonempty periods. The alphabet need not be finite.
-/
theorem lem_nm_survival_3 [Inhabited α] {u t : Word α} {s e : ℕ} (hc : Cross u t s e)
    (α₀ l : Word α) (hl : l ≠ []) (hn : ¬ Survives u t s e (prepend α₀ (periodicStream l))) :
    ¬ Keeps u t s e
      (streamPrefix (prepend α₀ (periodicStream l)) (α₀.length + l.length + offset u t s e - 1))
        := by
  exact lasso_breaking_prefix hc α₀ l hl hn

/-- **Corollary (Lasso completion)**, `cor:nm-lasso-completion`.
Form: Completion is split into cross completion and self completion. A default alphabet letter presents periodic streams; its value is irrelevant for nonempty periods. Neither a finite alphabet nor (FH) is needed. The completion implication does not require a pre-hole hypothesis.
-/
theorem cor_nm_lasso_completion [Inhabited α] {u t : Word α} {ξ : ℕ → α}
    (hl : I.Lasso (I.A.run u) ξ) (hf : I.SurvivorFree u t ξ)
    (hg : I.SelfSurvivorFree t ξ) :
    I.Completes u t (streamPrefix ξ (max u.length t.length + Fintype.card SA - 1)) ∧
      I.CompletesSelf t (streamPrefix ξ (max u.length t.length + Fintype.card SA - 1)) := by
  exact I.lasso_completes hl hf hg

/-- **Lemma (Infinite periodic words)**, `lem:nm-infinite`(1).
Form: StreamPeriod also permits the trivial zero shift; the original period p remains positive. The alphabet need not be finite.
-/
theorem lem_nm_infinite_1 {ξ : ℕ → α} {p q k : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hq : StreamPeriod (fun i => ξ (k + i)) q) :
    StreamPeriod ξ q := by
  exact period_of_suffix hp hξ hq

/-- **Lemma (Infinite periodic words)**, `lem:nm-infinite`(4).
Form: Lassos are represented by their eventual periods and prefix lengths. The alphabet need not be finite.
-/
theorem lem_nm_infinite_4 {ξ η : ℕ → α} {a b p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hξ : StreamPeriod (fun i => ξ (a + i)) p)
    (hη : StreamPeriod (fun i => η (b + i)) q)
    (he : ∀ i < max a b + p + q - 1, ξ i = η i) : ξ = η := by
  exact ultimately_periodic_agreement hp hq hξ hη he

/-- **Lemma (Invariant)**, `lem:nm-graph-invariant`.
Form: PreValid packages the node identity, spine safety, target openness and the two phase conditions. Neither a finite alphabet nor (FH) is needed. E may be any finite set of states.
-/
theorem lem_nm_graph_invariant [DecidableEq α] (E : Finset SA) {a b : PreNode SA SB SA' SB'}
    (p : (I.preHoleGraph E).Walk a b) (ha : (I.preHoleGraph E).initial a) :
    I.PreValid b p.left p.right := by
  exact I.toTwoWordInstance.preValid_walk E p ha

/-- **Lemma (Correctness of the pre-hole graph)**, `lem:nm-graph-correct`.
Form: Neither a finite alphabet nor (FH) is needed. E may be any finite set of states.
-/
theorem lem_nm_graph_correct [DecidableEq α] (E : Finset SA) (u t : Word α) :
    (I.preHoleGraph E).Accepts u t ↔ I.IsPreHole u t ∧ I.A.run u ∈ E := by
  exact I.toTwoWordInstance.preHoleGraph_correct E u t

/-- **Lemma (Good pairs)**, `lem:nm-good`.
Form: Survivor-freeness is the conjunction of its cross and self parts. Neither a finite alphabet nor (FH) is needed. The equivalence does not require periodicity of the stream.
-/
theorem lem_nm_good (ξ : ℕ → α) (u t : Word α) :
    I.PumpGood ξ u t ↔
      I.IsPreHole u t ∧ I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ := by
  let : Inhabited α := ⟨ξ 0⟩
  exact I.pumpGood_iff ξ u t

/-- **Lemma (Rests and periodic ends)**, `lem:nm-ends`(1).
Form: The words are the suffixes at the two periodic cuts; their lengths are the end distances. The alphabet need not be finite.
-/
theorem lem_nm_ends_1 {ξ : ℕ → α} {p : ℕ}
    (hp : LeastStreamPeriod ξ p) {u t : Word α}
    (hu : StreamPeriod (prepend u ξ) p) (ht : StreamPeriod (prepend t ξ) p) :
    prepend u ξ = prepend t ξ ↔ u.length % p = t.length % p := by
  exact periodic_ends_eq_iff hp hu ht

/-- **Lemma (Rests and periodic ends)**, `lem:nm-ends`(2).
Form: Rest distances are natural subtractions; equality also identifies periodic and rest cuts. Only the two periodic-split certificates and the suffix equality are assumed; p need not be positive or least. The alphabet need not be finite.
-/
theorem lem_nm_ends_2 {u t : Word α} {ru rt s e : ℕ}
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (hs : s ≤ u.length) (he : e ≤ t.length)
    (heq : prepend (u.drop s) ξ = prepend (t.drop e) ξ) : ru - s = rt - e := by
  exact PeriodicSplit.rest_length_eq hu ht hs he heq

/-- **Lemma (Rests and periodic ends)**, `lem:nm-ends`(3).
Form: The minimum bound is a conjunction of the two inequalities. The alphabet need not be finite.
-/
theorem lem_nm_ends_3 (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt s e : ℕ}
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (hne : u.length - ru ≠ t.length - rt) (hal : Aligned u t s e) :
    u.length - s ≤ u.length - ru ∧ u.length - s ≤ t.length - rt := by
  exact aligned_le_min hp hu ht hne hal

/-- **Lemma (Periodic target end)**, `lem:nm-target-end`.
Form: TargetOpen packages all proper cuts; the periodic end has length t.length - rt. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_target_end (hp : LeastStreamPeriod ξ p) {t : Word α} {rt : ℕ}
    (ht : PeriodicSplit ξ p t rt) (hopen : I.TargetOpen t) (hrej : I.B.run t ∈ I.Rej) :
    t.length - rt < Fintype.card SB * p := by
  exact I.toTwoWordInstance.periodicEnd_lt hp ht hopen hrej

/-- **Lemma (Non-self-similar words)**, `lem:nm-rigid`(1).
Form: The alphabet need not be finite.
-/
theorem lem_nm_rigid_1 {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p)
    {w : Word α} {r s : ℕ} (hw : PeriodicSplit ξ p w r) (hs : s < r) :
    NonSelfSimilar (prepend (w.drop s) ξ) := by
  exact nonSelfSimilar_of_rest hp hw hs

/-- **Lemma (Non-self-similar words)**, `lem:nm-rigid`(3).
Form: Uniqueness is equality of two cuts with the same non-self-similar suffix stream. The alphabet need not be finite. Cut uniqueness does not require periodicity of the appended stream.
-/
theorem lem_nm_rigid_3 {ξ : ℕ → α} {t : Word α} {e e₁ : ℕ}
    (hX : NonSelfSimilar (prepend (t.drop e₁) ξ)) (he : e ≤ t.length) (he₁ : e₁ ≤ t.length)
    (h : prepend (t.drop e) ξ = prepend (t.drop e₁) ξ) : e = e₁ := by
  exact cut_unique hX he he₁ h

/-- **Lemma (Non-self-similar words)**, `lem:nm-rigid`(4).
Form: The alphabet need not be finite.
-/
theorem lem_nm_rigid_4 (hp : LeastStreamPeriod ξ p) {v v' : Word α} {r j : ℕ}
    (hv : PeriodicSplit ξ p v r) (hj : j < r)
    (hun : ∀ e ≤ v'.length, prepend (v.drop j) ξ ≠ prepend (v'.drop e) ξ)
    {z : Word α} (k : ℕ) (hk : k ≤ v'.length) :
    prepend z (prepend (v.drop j) ξ) ≠ prepend (v'.drop k) ξ := by
  exact unpartnered_ext hp hv hj hun k hk

/-- **Lemma (Four deletions)**, `lem:nm-four`(1).
Form: N1 is the product-state cardinality; Shrinks packages a good pair with the same endpoint and smaller total length. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_four_1 (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h : t.length - rt + Fintype.card (SA × SA' × Fin p) ≤ u.length - ru) :
    I.Shrinks ξ u t := by
  exact I.shrink_spineEnd hp hg hu ht h

/-- **Lemma (Four deletions)**, `lem:nm-four`(2).
Form: P may be any finite set of partnered rest cuts, including all of C_u; N2 is its signature-space cardinality. Shrinks packages the conclusion. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_four_2 (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (P : Finset ℕ)
    (hP : ∀ j ∈ P, j < ru ∧ ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ)
    (h : Fintype.card (SA × SA' × SB × SB' × Bool) < P.card) : I.Shrinks ξ u t := by
  exact I.shrink_restSync hp hg hu ht P hP h

/-- **Lemma (Four deletions)**, `lem:nm-four`(3).
Form: P may be any finite set of unpartnered spine rest cuts, including U_u; N3 is its signature-space cardinality. Shrinks packages the conclusion. No periodic-split certificate for the target is needed. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_four_3 (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (P : Finset ℕ)
    (hP : ∀ j ∈ P, j < ru ∧ ∀ e ≤ t.length, prepend (u.drop j) ξ ≠ prepend (t.drop e) ξ)
    (h : Fintype.card (SA × SA') < P.card) : I.Shrinks ξ u t := by
  exact I.shrink_restU hp hg hu P hP h

/-- **Lemma (Four deletions)**, `lem:nm-four`(4).
Form: P may be any finite set of unpartnered target rest cuts, including U_t; N4 is its signature-space cardinality. Shrinks packages the conclusion. No periodic-split certificate for the spine is needed. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_four_4 (hp : LeastStreamPeriod ξ p) {u t : Word α} {rt : ℕ}
    (hg : I.PumpGood ξ u t) (ht : PeriodicSplit ξ p t rt) (P : Finset ℕ)
    (hP : ∀ e ∈ P, e < rt ∧ ∀ s ≤ u.length, prepend (t.drop e) ξ ≠ prepend (u.drop s) ξ)
    (h : Fintype.card (SB × SB') < P.card) : I.Shrinks ξ u t := by
  exact I.shrink_restT hp hg ht P hP h

/-- **Lemma (Continuation identity)**, `lem:nm-continuation`(1).
Form: State preservation is quantified over an arbitrary automaton, and thus includes all four readers on either word. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_continuation_1 {t : Word α} {j : ℕ} (hj : I.J t = some j) (θ : Word α) :
    I.J (t ++ θ) = some j ∧
    ∀ (S : Type*) (M : LDFA α S) (w : Word α) (s : ℕ), s ≤ w.length →
      M.atCut (w ++ θ) s = M.atCut w s :=
  ⟨I.toTwoWordInstance.J_append hj θ, fun _ M w _ hs => M.atCut_append w θ hs⟩

/-- **Lemma (Continuation identity)**, `lem:nm-continuation`(2).
Form: Cross includes both cut bounds, including s ≤ |u|; self comparisons specialize the same identity to u = t and strict cuts. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_continuation_2 {u t θ : Word α} {s e j : ℕ}
    (hj : I.J t = some j) (he : e ≤ j) :
    Cross (u ++ θ) (t ++ θ) s e ↔ Cross u t s e ∧ Keeps u t s e θ :=
  cross_append_iff (he.trans ((I.J_eq_some_iff t j).mp hj).2.1)

/-- **Lemma (Continuation identity)**, `lem:nm-continuation`(3).
Form: Keeps is defined by the overhang prefix test; self comparisons specialize cross comparisons to equal words. The periodic stream of a nonempty overhang takes its default letter from the overhang itself, so the alphabet may be empty; it need not be finite.
-/
theorem lem_nm_continuation_3 (u t θ : Word α) (s e : ℕ) :
    (Keeps u t s e θ ↔ θ.IsPrefix (overhang u t s e ++ θ)) ∧
    (∀ hn : overhang u t s e ≠ [],
      letI : Inhabited α := ⟨(overhang u t s e).head hn⟩
      (Keeps u t s e θ ↔ IsStreamPrefix θ (periodicStream (overhang u t s e)))) ∧
    (Aligned u t s e → Keeps u t s e θ) :=
  ⟨Iff.rfl, fun hn =>
    letI : Inhabited α := ⟨(overhang u t s e).head hn⟩
    periodic_prefix_iff hn, fun ha => aligned_keeps ha θ⟩

/-- **Lemma (Decomposition at the first rejected cut)**, `lem:nm-decomposition`.
Form: Completion is split into cross and self parts; the rejected cut is the length of the pre-hole target, whose J equals that length by definition. The alphabet need not be finite.
-/
theorem lem_nm_decomposition :
    (∀ u t θ, I.IsPreHole u t → I.Completes u t θ → I.CompletesSelf t θ →
      I.IsHole (u ++ θ) (t ++ θ)) ∧
    (I.ForcedHeads → ∀ u t, I.IsHole u t →
      ∃ u₀ t₀ θ, u = u₀ ++ θ ∧ t = t₀ ++ θ ∧ θ = t.drop t₀.length ∧
        I.IsPreHole u₀ t₀ ∧ I.Completes u₀ t₀ θ ∧ I.CompletesSelf t₀ θ) :=
  ⟨fun _ _ _ => I.preHole_complete, fun hf _ _ => I.hole_decomposition hf⟩

/-- **Lemma (Breaker)**, `lem:nm-breaker`.
Form: The periodic prefix test is written θ ≤prefix oθ, equivalent to θ ≤prefix o^ω for nonempty o; completion has cross and self parts. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_breaker :
    (∀ q, I.Branching q → ∀ W, ∃ θ, I.SafeFrom q θ ∧
      θ.length ≤ W + 3 * Fintype.card SA ∧
      ∀ o : Word α, o ≠ [] → o.length ≤ W → ¬ θ.IsPrefix (o ++ θ)) ∧
    (∀ u t, I.IsPreHole u t → I.Branching (I.A.run u) →
      ∃ θ, I.Completes u t θ ∧ I.CompletesSelf t θ ∧
        θ.length ≤ max u.length t.length + 3 * Fintype.card SA) :=
by
  constructor
  · intro q hb W
    obtain ⟨_, r, _, _, a, _⟩ := (show I.Branching _ from hb)
    let : Inhabited α := ⟨a⟩
    exact I.breakerM hb W
  · intro u t hp hb
    obtain ⟨_, r, _, _, a, _⟩ := (show I.Branching _ from hb)
    let : Inhabited α := ⟨a⟩
    exact I.preHole_breaker hp hb

/-- **Lemma (Thin states)**, `lem:nm-thin`(3).
Form: A default alphabet letter presents periodic streams; its value is irrelevant for nonempty periods. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_thin_3 [Inhabited α] {q : SA} (hq : I.Thin q) :
    (∀ ξ, I.InfiniteSafe q ξ → I.Lasso q ξ) ∧ ∃ ξ, I.Lasso q ξ := by
  refine ⟨fun _ => I.toTwoWordInstance.thin_lasso hq, ?_⟩
  have hv : I.Viable q := by
    by_contra hn
    exact hq.2.1 ⟨hq.1, hn⟩
  obtain ⟨ξ, hξ⟩ := (I.viable_iff q).mp hv
  exact ⟨ξ, I.toTwoWordInstance.thin_lasso hq hξ⟩

/-- **Lemma (Survival)**, `lem:nm-survival`(1).
Form: Non-alignment is equivalent to a nonempty overhang for a comparison; self comparisons are the strict equal-word specialization. A default alphabet letter presents periodic streams; its value is irrelevant for nonempty periods. The alphabet need not be finite.
-/
theorem lem_nm_survival_1 [Inhabited α] {u t : Word α} {s e : ℕ}
    (hc : Cross u t s e) (ξ : ℕ → α) :
    (¬ Aligned u t s e → (Survives u t s e ξ ↔ ξ = periodicStream (overhang u t s e))) ∧
    (Aligned u t s e → Survives u t s e ξ) :=
  ⟨fun hn => survives_iff_periodic hc hn ξ, fun ha => aligned_survives ha ξ⟩

/-- **Proposition (Short pre-holes)**, `prop:nm-short-prehole`.
Form: E is a finite set of states; the result holds without requiring its members to be safe. Decidability is a computable definition, the executable bounded search TwoWordInstance.preHoleExistsDecidable over pairs of words of length at most 12aba'b'. (FH) is not needed.
-/
def prop_nm_short_prehole [Fintype α] [DecidableEq α] (E : Finset SA) :
    Decidable (∃ u t, I.IsPreHole u t ∧ I.A.run u ∈ E) ×'
    (∀ u t, I.IsPreHole u t → I.A.run u ∈ E →
      ∃ v w, I.IsPreHole v w ∧ I.A.run v ∈ E ∧
        v.length < 12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB' ∧
        w.length < 12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB') :=
  ⟨I.toTwoWordInstance.preHoleExistsDecidable E,
    fun _ _ => I.toTwoWordInstance.short_preHole E⟩

/-- **Lemma (Aperiodic lassos)**, `lem:nm-aperiodic`.
Form: Self comparisons specialize cross comparisons to equal words; survivor-freeness has cross and self parts. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_aperiodic {ξ : ℕ → α}
    (hn : ¬ ∃ p, 0 < p ∧ StreamPeriod ξ p) :
    (∀ u t s e, Cross u t s e → ¬ Aligned u t s e → ¬ Survives u t s e ξ) ∧
    (∀ u t, I.IsPreHole u t → I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ) := by
  let : Inhabited α := ⟨ξ 0⟩
  refine ⟨?_, fun _ _ hp => ⟨I.toTwoWordInstance.aperiodic_survivorFree hp hn,
    I.aperiodic_selfSurvivorFree hn⟩⟩
  intro u t s e hc ha hs
  have he := (survives_iff_periodic hc ha ξ).mp hs
  apply hn
  refine ⟨(overhang u t s e).length, ?_, he ▸ periodicStream_period _⟩
  have hh := cross_aligned_iff hc
  exact List.length_pos_iff.mpr (fun hz => ha (hh.mpr hz))

/-- **Theorem (Pump)**, `thm:nm-pump`.
Form: pumpBound is the displayed polynomial and pumpCapacity is Pcap; survivor-freeness has cross and self parts. Neither a finite alphabet nor (FH) is needed.
-/
theorem thm_nm_pump (hp : LeastStreamPeriod ξ p) {u t : Word α}
    (hph : I.IsPreHole u t) (hsf : I.SurvivorFree u t ξ) (hself : I.SelfSurvivorFree t ξ) :
    ∃ u' t', I.IsPreHole u' t' ∧ I.SurvivorFree u' t' ξ ∧ I.SelfSurvivorFree t' ξ ∧
      I.A.run u' = I.A.run u ∧
      u'.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p ∧
      t'.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p ∧
      (p ≤ Fintype.card SA →
        u'.length < pumpCapacity (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') ∧
        t'.length < pumpCapacity (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB')) := by
  let : Inhabited α := ⟨ξ 0⟩
  obtain ⟨u', t', hh, hf, hs, he, hu, ht⟩ := I.pump hp hph hsf hself
  exact ⟨u', t', hh, hf, hs, he, hu, ht,
    fun h => ⟨hu.trans_le (pumpBound_le_capacity h), ht.trans_le (pumpBound_le_capacity h)⟩⟩
/-- **Lemma (Infinite periodic words)**, `lem:nm-infinite`(2).
Form: Under the least-period hypothesis on xi, periods of suffixes are quantified directly; choosing k = |alpha| and q = |lambda| gives the lasso consequence. The suffix also retains the least period. The alphabet need not be finite.
-/
theorem lem_nm_infinite_2 (hp : LeastStreamPeriod ξ p) :
    (∀ k, LeastStreamPeriod (fun i => ξ (k + i)) p) ∧
    (∀ i j, (fun n => ξ (i + n)) = (fun n => ξ (j + n)) ↔ i % p = j % p) ∧
    (∀ k q, 0 < q → StreamPeriod (fun i => ξ (k + i)) q →
      StreamPeriod ξ q ∧ p ≤ q) :=
  ⟨leastPeriod_suffix hp, leastPeriod_suffix_eq_iff hp,
    fun _ q hq h => ⟨period_of_suffix hp.1 hp.2.1 h,
      hp.2.2 q hq (period_of_suffix hp.1 hp.2.1 h)⟩⟩

/-- **Lemma (Infinite periodic words)**, `lem:nm-infinite`(3).
Form: A default alphabet letter presents periodic streams; its value is irrelevant for nonempty periods. The alphabet need not be finite.
-/
theorem lem_nm_infinite_3 [Inhabited α] (o : Word α) (ho : o ≠ []) (ξ : ℕ → α) :
    ((∀ k, IsStreamPrefix (streamPrefix ξ k) (periodicStream o)) → ξ = periodicStream o) ∧
    (prepend o ξ = ξ → ξ = periodicStream o ∧ StreamPeriod ξ o.length) := by
  refine ⟨?_, fun h => ⟨(prepend_fixed_iff ho).mp h,
    (prepend_fixed_iff ho).mp h ▸ periodicStream_period o⟩⟩
  intro h
  funext i
  have hh := (streamPrefix_iff.mp (h (i + 1))) i (by simp)
  simpa only [streamPrefix, List.getElem_ofFn] using hh

/-- **Lemma (Aligned pairs under extension)**, `lem:nm-hit`(1).
Form: The alphabet need not be finite.
-/
theorem lem_nm_hit_1 (u t : Word α) (s e : ℕ) :
    (Aligned u [] s e ↔ s = u.length ∧ e = 0) ∧
    (Aligned [] t s e ↔ s = 0 ∧ e = t.length) := aligned_empty u t s e

/-- **Lemma (Aligned pairs under extension)**, `lem:nm-hit`(2).
Form: The raw cut characterization is paired with the AlignedHit identity for an arbitrary relation, which includes both guard and head hit bits. The alphabet need not be finite. The automaton state carriers need not be finite.
-/
theorem lem_nm_hit_2 {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) (u t : Word α) (c d : α) :
    (∀ s e, Aligned (u ++ [c]) (t ++ [d]) s e ↔
      (s = u.length + 1 ∧ e = t.length + 1) ∨ (c = d ∧ Aligned u t s e)) ∧
    (AlignedHit M N R (u ++ [c]) (t ++ [d]) ↔
      R (M.run (u ++ [c])) (N.run (t ++ [d])) ∨ (c = d ∧ AlignedHit M N R u t)) :=
  ⟨aligned_snoc u t c d, alignedHit_snoc M N R u t c d⟩

/-- **Lemma (Non-self-similar words)**, `lem:nm-rigid`(2).
Form: The alphabet need not be finite.
-/
theorem lem_nm_rigid_2 {ξ : ℕ → α} (h : NonSelfSimilar ξ) :
    (∀ z₁ z₂, prepend z₁ ξ = prepend z₂ ξ → z₁ = z₂) ∧
    (∀ z : Word α, z ≠ [] → ∀ k, prepend z ξ ≠ fun i => ξ (k + i)) :=
  ⟨fun _ _ => h.prepend_inj, fun _ hn => h.ne_shift hn⟩

/-- **Lemma (Two ways to lift matched pairs)**, `lem:nm-dischargers`(1).
Form: Absorption is stated for an arbitrary prefix and target stream, encompassing implication (ii). Periodicity of the stream is not needed. The alphabet need not be finite.
-/
theorem lem_nm_dischargers_1 {Y Z : ℕ → α} {w : Word α}
    (h : prepend w Y = Y) (x : Word α) (hx : prepend x Y = Z) :
    prepend (x ++ w) Y = Z := by
  simpa only [prepend_assoc, h] using hx

/-- **Lemma (Two ways to lift matched pairs)**, `lem:nm-dischargers`(2).
Form: The two impossible premises are stated directly for deep-deep and deep-shallow self pairs. The appended stream need not be periodic. The alphabet need not be finite.
-/
theorem lem_nm_dischargers_2 {ξ : ℕ → α} {y : Word α}
    (h : NonSelfSimilar (prepend y ξ)) (x : Word α) :
    (∀ i j, i < j → j < x.length →
      prepend (x.drop i ++ y) ξ ≠ prepend (x.drop j ++ y) ξ) ∧
    (∀ i, i < x.length → ∀ k, k ≤ y.length →
      prepend (x.drop i ++ y) ξ ≠ prepend (y.drop k) ξ) := by
  constructor
  · intro i j hij hj he
    have hl := congrArg List.length (h.prepend_inj (by simpa only [prepend_assoc] using he))
    simp only [List.length_drop] at hl
    omega
  · intro i hi k hk he
    apply h.ne_shift (z := x.drop i) (List.ne_nil_of_length_pos (by simp; omega)) k
    simpa only [prepend_assoc, ← prepend_shift y ξ hk] using he

/-- **Lemma (Deletion)**, `lem:nm-deletion`(1).
Form: The three numbered premises are jointly required in each entry. D1 uses loop equations, D2 is expanded into the five deep/shallow implications (wholly shallow pairs lift automatically), and D3 is the surviving-head disjunction. The output is the specified deleted pair. Neither a finite alphabet nor (FH) is needed. The deletion lemma holds for arbitrary streams.
-/
theorem lem_nm_deletion_1 {ξ : ℕ → α} {x w y x' w' y' : Word α}
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
    (hSS : ∀ i j, i < j → j < x'.length →
      prepend (x'.drop i ++ y') ξ = prepend (x'.drop j ++ y') ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (x'.drop j ++ w' ++ y') ξ)
    (hS : ∀ i < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop i ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (y'.drop k) ξ)
    (hpos : w ≠ [] ∨ w' ≠ [])
    (hhead : ∃ s e, I.HeadEvent (x ++ w ++ y) (x' ++ w' ++ y') s e ∧
      ((x.length + w.length ≤ s ∧ x'.length + w'.length ≤ e) ∨
        (s ≤ x.length ∧ e ≤ x'.length ∧ x.length - s = x'.length - e ∧
          w.length = w'.length))) :
    I.PumpGood ξ (x ++ y) (x' ++ y') ∧ I.A.run (x ++ y) = I.A.run (x ++ w ++ y) ∧
      (x ++ y).length + (x' ++ y').length <
        (x ++ w ++ y).length + (x' ++ w' ++ y').length := by
  exact I.delete_good hg hA hA' hB hB' hDD hDS hSD hSS hS hpos hhead

/-- **Lemma (Deletion)**, `lem:nm-deletion`(2).
Form: The three numbered premises are jointly required in each entry. D1 uses loop equations, D2 is expanded into the five deep/shallow implications (wholly shallow pairs lift automatically), and D3 is the surviving-head disjunction. The output is the specified deleted pair. Neither a finite alphabet nor (FH) is needed. The deletion lemma holds for arbitrary streams.
-/
theorem lem_nm_deletion_2 {ξ : ℕ → α} {x w y x' w' y' : Word α}
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
    (hSS : ∀ i j, i < j → j < x'.length →
      prepend (x'.drop i ++ y') ξ = prepend (x'.drop j ++ y') ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (x'.drop j ++ w' ++ y') ξ)
    (hS : ∀ i < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop i ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (y'.drop k) ξ)
    (hpos : w ≠ [] ∨ w' ≠ [])
    (hhead : ∃ s e, I.HeadEvent (x ++ w ++ y) (x' ++ w' ++ y') s e ∧
      ((x.length + w.length ≤ s ∧ x'.length + w'.length ≤ e) ∨
        (s ≤ x.length ∧ e ≤ x'.length ∧ x.length - s = x'.length - e ∧
          w.length = w'.length))) :
    I.PumpGood ξ (x ++ y) (x' ++ y') ∧ I.A.run (x ++ y) = I.A.run (x ++ w ++ y) ∧
      (x ++ y).length + (x' ++ y').length <
        (x ++ w ++ y).length + (x' ++ w' ++ y').length := by
  exact I.delete_good hg hA hA' hB hB' hDD hDS hSD hSS hS hpos hhead

/-- **Lemma (Deletion)**, `lem:nm-deletion`(3).
Form: The three numbered premises are jointly required in each entry. D1 uses loop equations, D2 is expanded into the five deep/shallow implications (wholly shallow pairs lift automatically), and D3 is the surviving-head disjunction. The output is the specified deleted pair. Neither a finite alphabet nor (FH) is needed. The deletion lemma holds for arbitrary streams.
-/
theorem lem_nm_deletion_3 {ξ : ℕ → α} {x w y x' w' y' : Word α}
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
    (hSS : ∀ i j, i < j → j < x'.length →
      prepend (x'.drop i ++ y') ξ = prepend (x'.drop j ++ y') ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (x'.drop j ++ w' ++ y') ξ)
    (hS : ∀ i < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop i ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop i ++ w' ++ y') ξ = prepend (y'.drop k) ξ)
    (hpos : w ≠ [] ∨ w' ≠ [])
    (hhead : ∃ s e, I.HeadEvent (x ++ w ++ y) (x' ++ w' ++ y') s e ∧
      ((x.length + w.length ≤ s ∧ x'.length + w'.length ≤ e) ∨
        (s ≤ x.length ∧ e ≤ x'.length ∧ x.length - s = x'.length - e ∧
          w.length = w'.length))) :
    I.PumpGood ξ (x ++ y) (x' ++ y') ∧ I.A.run (x ++ y) = I.A.run (x ++ w ++ y) ∧
      (x ++ y).length + (x' ++ y').length <
        (x ++ w ++ y).length + (x' ++ w' ++ y').length := by
  exact I.delete_good hg hA hA' hB hB' hDD hDS hSD hSS hS hpos hhead

/-- **Lemma (Counting)**, `lem:nm-count`.
Form: partnered and unpartnered enumerate C and U; signature cardinalities express N1 through N4, and pumpBound is their sum plus b times the period. Neither a finite alphabet nor (FH) is needed.
-/
theorem lem_nm_count {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p)
    {u t : Word α} {ru rt : ℕ} (hg : I.PumpGood ξ u t)
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h1 : u.length - ru < t.length - rt + Fintype.card (SA × SA' × Fin p))
    (h2 : (SelfTwoWordInstance.partnered ξ u t ru).card ≤ Fintype.card (SA × SA' × SB × SB' × Bool))
    (h3 : (SelfTwoWordInstance.unpartnered ξ u t ru).card ≤ Fintype.card (SA × SA'))
    (h4 : (SelfTwoWordInstance.unpartnered ξ t u rt).card ≤ Fintype.card (SB × SB')) :
    u.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p ∧
    t.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p := by
  exact I.count_short hp hg hu ht h1 h2 h3 h4


/-- **Theorem (Three cases)**, `thm:nm-three-cases`(1).
Form: State carriers are finite initial segments; pumpHoleBound is Lnm. This item gives branching completion with its bound, without (FH).
-/
theorem thm_nm_three_cases_1 [Fintype α] [DecidableEq α] {a b c d : ℕ}
    (I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d)) {u t : Word α}
    (hp : I.IsPreHole u t) (hb : I.Branching (I.A.run u)) :
    ∃ v w, I.IsHole v w ∧ v.length + w.length ≤ pumpHoleBound a b c d :=
  nonMortalShortHoleBoundSelf a b c d I ⟨u, t, hp, Or.inl hb⟩

/-- **Theorem (Three cases)**, `thm:nm-three-cases`(2).
Form: State carriers are finite initial segments; survivor-freeness has cross and self parts. Includes the exact prefix claim for a completed hole and the Lnm bound without (FH).
-/
theorem thm_nm_three_cases_2 [Fintype α] [DecidableEq α] {a b c d : ℕ}
    (I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d)) :
    (∀ u t, I.IsPreHole u t → I.Thin (I.A.run u) →
      (∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ) →
      ∃ v w, I.IsHole v w ∧ v.length + w.length ≤ pumpHoleBound a b c d) ∧
    (∀ u t θ, I.IsPreHole u t → I.Thin (I.A.run u) →
      I.Completes u t θ → I.CompletesSelf t θ → ¬ I.Mortal (I.A.run (u ++ θ)) →
      ∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ ∧
        I.SelfSurvivorFree t ξ ∧ streamPrefix ξ θ.length = θ) :=
  ⟨fun u t hp ht hξ => nonMortalShortHoleBoundSelf a b c d I ⟨u, t, hp, Or.inr ⟨ht, hξ⟩⟩,
    fun _ _ _ hp _ => I.thin_completion_stream hp⟩

/-- **Theorem (Three cases)**, `thm:nm-three-cases`(3).
Form: NonMortalCase is the disjunction of the branching and thin survivor-free pre-hole cases. Includes the theorem's full equivalence and its original-hole mortal alternative. The alphabet need not be finite.
-/
theorem thm_nm_three_cases_3 (hf : I.ForcedHeads) :
    (I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole) ∧
    (∀ u t θ, I.IsPreHole u t → I.Completes u t θ → I.CompletesSelf t θ →
      ¬ I.Branching (I.A.run u) →
      ¬ (I.Thin (I.A.run u) ∧ ¬ I.Mortal (I.A.run (u ++ θ))) →
      I.IsMortalHole (u ++ θ) (t ++ θ)) :=
  ⟨I.three_cases_total hf, fun _ _ _ => I.completion_mortal⟩

/-- **Corollary (Short holes outside the mortal case)**, `cor:nm-short-holes`.
Form: State carriers are finite initial segments and pumpHoleBound is Lnm.
-/
theorem cor_nm_short_holes [Fintype α] [DecidableEq α] {a b c d : ℕ}
    (I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d)) (hf : I.ForcedHeads) :
    I.HasHole ↔ (∃ u t, I.IsHole u t ∧ u.length + t.length ≤ pumpHoleBound a b c d) ∨
      I.HasMortalHole := by
  constructor
  · intro h
    rcases (I.three_cases_total hf).mp h with hn | hm
    · exact Or.inl (nonMortalShortHoleBoundSelf a b c d I hn)
    · exact Or.inr hm
  · rintro (⟨u, t, hh, _⟩ | ⟨u, t, hh⟩)
    · exact ⟨u, t, hh⟩
    · exact ⟨u, t, hh.1⟩
end DeciENSSE.Paper
