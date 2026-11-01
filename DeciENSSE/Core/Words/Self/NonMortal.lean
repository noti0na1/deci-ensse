import DeciENSSE.Core.Words.Self.Basic
import DeciENSSE.Core.Words.Pump

/-! # Non-mortal holes with target self events

Decomposition and completion extend to target self events. Branching and
aperiodic witnesses are bounded. Periodic shortening, proved in `Self.Pump`,
supplies the third case of the non-mortal bound.

## Main declarations

- `SelfTwoWordInstance.hole_decomposition`
- `three_cases_self`
- `nonMortalShortHoleBoundSelf_of_periodic`
-/

namespace DeciENSSE.Core.Words.Self
open DeciNSSE.RejectedTail

variable {α : Type*}
namespace SelfTwoWordInstance
open DeciENSSE.Core.Words.TwoWordInstance

variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
variable (I : SelfTwoWordInstance α SA SB SC SD)

/-- The first rejection prevents new self cuts in the continuation. -/
theorem selfEvent_append_iff {t θ : Word α} {i k j : ℕ}
    (hj : I.J t = some j) :
    I.SelfEvent (t ++ θ) i k ↔ I.SelfEvent t i k ∧ TwoWordInstance.Keeps t t i k θ := by
  have hja := I.toTwoWordInstance.J_append hj θ
  have hjl := ((I.J_eq_some_iff t j).mp hj).2.1
  constructor
  · rintro ⟨hik, hc, ⟨j', hj', hk⟩, hg⟩
    have heq : j' = j := by simpa [hja] using hj'.symm
    subst j'
    obtain ⟨hc, hkeep⟩ := (cross_append_iff (le_trans hk hjl)).mp hc
    refine ⟨⟨hik, hc, ⟨j, by simp [hj], hk⟩, ?_⟩, hkeep⟩
    simpa [LDFA.atCut_append _ _ _ hc.1,
      LDFA.atCut_append _ _ _ hc.2.1] using hg
  · rintro ⟨⟨hik, hc, hk, hg⟩, hkeep⟩
    refine ⟨hik, (cross_append_iff hc.2.1).mpr ⟨hc, hkeep⟩, ?_, ?_⟩
    · simpa [hja, hj] using hk
    · simpa [LDFA.atCut_append _ _ _ hc.1,
        LDFA.atCut_append _ _ _ hc.2.1] using hg

/-- Break both event families to complete a signed hole. -/
theorem preHole_complete {u t θ : Word α} (hp : I.IsPreHole u t)
    (hc : I.Completes u t θ) (hs : I.CompletesSelf t θ) :
    I.IsHole (u ++ θ) (t ++ θ) := by
  refine ⟨I.toTwoWordInstance.preHole_complete hp hc, (I.noSelf_iff _).mpr ?_⟩
  intro i j he
  obtain ⟨he, hk⟩ := (I.selfEvent_append_iff hp.2.1).mp he
  exact hs i j he hk

/-- Decomposition retains the exact rejected suffix and both completions. -/
theorem hole_decomposition {u t : Word α} (hf : I.ForcedHeads) (hh : I.IsHole u t) :
    ∃ u₀ t₀ θ, u = u₀ ++ θ ∧ t = t₀ ++ θ ∧ θ = t.drop t₀.length ∧
      I.IsPreHole u₀ t₀ ∧ I.Completes u₀ t₀ θ ∧ I.CompletesSelf t₀ θ := by
  obtain ⟨u₀, t₀, θ, hu, ht, hθ, hp, hc⟩ := I.toTwoWordInstance.hole_decomposition hf hh.1
  refine ⟨u₀, t₀, θ, hu, ht, hθ, hp, hc, ?_⟩
  intro i j he hk
  have hnew := (I.selfEvent_append_iff hp.2.1).mpr ⟨he, hk⟩
  exact (I.noSelf_iff t).mp hh.2 i j (ht ▸ hnew)

/-- One safe departure breaks every nonempty overhang of length at most M. -/
theorem breakerM [Inhabited α] {q : SA} (hb : I.Branching q) (M : ℕ) :
    ∃ θ, I.SafeFrom q θ ∧ θ.length ≤ M + 3 * Fintype.card SA ∧
      ∀ o : Word α, o ≠ [] → o.length ≤ M → ¬ θ.IsPrefix (o ++ θ) := by
  classical
  obtain ⟨r, hr, hcyc, a, b, hab, ha, hb'⟩ := hb.2
  obtain ⟨α₀, hα, hαr, hαlen⟩ := I.toTwoWordInstance.short_safeReachable hr
  obtain ⟨l, hln, hl, hlr, hllen⟩ := I.toTwoWordInstance.short_cyclic hcyc
  have hlpos := List.length_pos_iff.mpr hln
  let k := M / l.length + 2
  let n := k * l.length
  have hnlo : M + l.length ≤ n := by
    have hm := Nat.mod_lt M hlpos
    have hd := Nat.mod_add_div M l.length
    dsimp [n, k]
    rw [Nat.add_mul, Nat.mul_comm (M / l.length) l.length]
    omega
  have hnhi : n ≤ M + 2 * l.length := by
    have hd := Nat.mod_add_div M l.length
    dsimp [n, k]
    rw [Nat.add_mul, Nat.mul_comm (M / l.length) l.length]
    omega
  let c := if a = periodicStream l n then b else a
  have hcne : c ≠ periodicStream l n := by
    dsimp [c]
    split_ifs with h
    · exact fun he => hab (h.trans he.symm)
    · exact h
  have hcsafe : I.A.step r c ∉ I.Bad := by
    dsimp [c]
    split_ifs <;> assumption
  let θ := α₀ ++ streamPrefix (periodicStream l) n ++ [c]
  have hs := I.toTwoWordInstance.cycle_infiniteSafe hln hl hlr
  have hrun : I.toTwoWordInstance.A.runFrom r (streamPrefix (periodicStream l) n) = r := by
    rw [← LDFA.streamRun_eq]; exact I.toTwoWordInstance.cycle_streamRun_mul hln hlr k
  refine ⟨θ, ?_, ?_, ?_⟩
  · apply I.toTwoWordInstance.safeFrom_append.mpr
    refine ⟨I.toTwoWordInstance.safeFrom_append.mpr ⟨hα, ?_⟩, ?_⟩
    · rw [hαr]; exact I.toTwoWordInstance.infiniteSafe_prefix hs n
    · rw [LDFA.runFrom_append, hαr, hrun]
      apply I.toTwoWordInstance.safeFrom_cons.mpr
      refine ⟨I.toTwoWordInstance.safeFrom_start hl, ?_⟩
      simpa [SafeFrom] using hcsafe
  · simp only [θ, List.length_append, streamPrefix_length, List.length_singleton]
    omega
  · intro o ho hlen hk
    exact periodic_departure_breaks ho hln α₀ n (by omega) c hcne
      ((periodic_prefix_iff ho).mp hk)

/-- The offset maximum covers cross overhangs and target self overhangs. -/
theorem preHole_breaker [Inhabited α] {u t : Word α} (hp : I.IsPreHole u t)
    (hb : I.Branching (I.A.run u)) :
    ∃ θ, I.Completes u t θ ∧ I.CompletesSelf t θ ∧
      θ.length ≤ max u.length t.length + 3 * Fintype.card SA := by
  obtain ⟨θ, hs, hl, hbreak⟩ := I.breakerM hb (max u.length t.length)
  refine ⟨θ, ⟨hs, ?_⟩, ?_, hl⟩
  · intro s e he
    have ha : ¬ TwoWordInstance.Aligned u t s e := by
      intro ha
      exact hp.2.2.2 s (Finset.mem_range.mpr (by have := he.1.1; omega))
        e (Finset.mem_range.mpr (by have := he.1.2.1; omega)) ⟨he, ha⟩
    apply hbreak _ (fun h => ha ((cross_aligned_iff he.1).mpr h))
    rw [overhang_length]
    exact (cross_offset_le he.1).trans (le_max_left _ _)
  · intro i j he
    apply hbreak _ (fun h => I.selfEvent_not_aligned he
      ((cross_aligned_iff he.2.1).mpr h))
    rw [overhang_length]
    exact (cross_offset_le he.2.1).trans (le_max_right _ _)

/-- A longer continuation cannot restore a broken self comparison. -/
theorem completesSelf_mono {t θ ψ : Word α} (hc : I.CompletesSelf t θ)
    (hp : θ.IsPrefix ψ) : I.CompletesSelf t ψ := by
  intro i j he hk
  exact hc i j he (keeps_prefix hk hp)

/-- The finite self-event family has a common breaking prefix. -/
theorem selfSurvivorFree_completes {t : Word α} {ξ : ℕ → α}
    (hg : I.SelfSurvivorFree t ξ) :
    ∃ n, I.CompletesSelf t (streamPrefix ξ n) := by
  classical
  let P := Fin (t.length + 1) × Fin (t.length + 1)
  have hb (p : P) : ∃ n, I.SelfEvent t p.1 p.2 →
      ¬ TwoWordInstance.Keeps t t p.1 p.2 (streamPrefix ξ n) := by
    by_cases he : I.SelfEvent t p.1 p.2
    · have hn : ¬ ∀ n, TwoWordInstance.Keeps t t p.1 p.2 (streamPrefix ξ n) := by
        intro h
        exact hg _ _ he ((survives_iff_keeps he.2.1 ξ).mpr h)
      obtain ⟨n, hn⟩ := not_forall.mp hn
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (he h).elim⟩
  choose n hn using hb
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro i j he hk
  let p : P := (⟨i, by have := he.2.1.1; omega⟩,
    ⟨j, by have := he.2.1.2.1; omega⟩)
  have hle : n p ≤ N := Finset.le_sup (f := n) (Finset.mem_univ p)
  exact hn p he (keeps_prefix hk (streamPrefix_prefix ξ hle))

/-- Take the maximum of the two finite event families' breaking lengths. -/
theorem survivorFree_completes {u t : Word α} {ξ : ℕ → α}
    (hs : I.InfiniteSafe (I.A.run u) ξ) (hf : I.SurvivorFree u t ξ)
    (hg : I.SelfSurvivorFree t ξ) :
    ∃ n, I.Completes u t (streamPrefix ξ n) ∧
      I.CompletesSelf t (streamPrefix ξ n) := by
  obtain ⟨n, hn⟩ := I.toTwoWordInstance.survivorFree_completes hs hf
  obtain ⟨m, hm⟩ := I.selfSurvivorFree_completes hg
  refine ⟨max n m, ⟨I.toTwoWordInstance.infiniteSafe_prefix hs _, ?_⟩,
    I.completesSelf_mono hm (streamPrefix_prefix ξ (le_max_right _ _))⟩
  intro s e he hk
  exact hn.2 s e he (keeps_prefix hk (streamPrefix_prefix ξ (le_max_left _ _)))

/-- A finite self completion excludes self survivors on any extending stream. -/
theorem completesSelf_survivorFree {t θ : Word α} {ξ : ℕ → α}
    (hc : I.CompletesSelf t θ) (hp : IsStreamPrefix θ ξ) :
    I.SelfSurvivorFree t ξ := by
  intro i j he hs
  have hk := (survives_iff_keeps he.2.1 ξ).mp hs θ.length
  rw [hp] at hk
  exact hc i j he hk

/-- A completed prefix breaks both event families. -/
theorem completes_survivorFree {u t θ : Word α} {ξ : ℕ → α}
    (hc : I.Completes u t θ) (hg : I.CompletesSelf t θ) (hp : IsStreamPrefix θ ξ) :
    I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ :=
  ⟨I.toTwoWordInstance.completes_survivorFree hc hp, I.completesSelf_survivorFree hg hp⟩

/-- The common safe breaking prefix completes a signed hole. -/
theorem hasHole_of_survivorFree {u t : Word α} (hp : I.IsPreHole u t)
    {ξ : ℕ → α} (hs : I.InfiniteSafe (I.A.run u) ξ)
    (hf : I.SurvivorFree u t ξ) (hg : I.SelfSurvivorFree t ξ) : I.HasHole := by
  obtain ⟨n, hc, hg⟩ := I.survivorFree_completes hs hf hg
  exact ⟨u ++ streamPrefix ξ n, t ++ streamPrefix ξ n, I.preHole_complete hp hc hg⟩

/-- The original signed hole is retained in the mortal branch. -/
theorem cases_of_hole (hf : I.ForcedHeads) (hh : I.HasHole) :
    I.NonMortalCase ∨ I.HasMortalHole := by
  classical
  obtain ⟨u, t, hh⟩ := hh
  obtain ⟨u₀, t₀, θ, hu, ht, _, hp, hc, hg⟩ := I.hole_decomposition hf hh
  have hq : I.A.run u₀ ∉ I.Bad := I.toTwoWordInstance.safeFrom_end hp.1
  have hj : I.J t = some t₀.length := by
    rw [ht]; exact I.toTwoWordInstance.J_append hp.2.1 θ
  have htail : t.length - t₀.length = θ.length := by simp [ht]
  have hend : I.A.run u = I.A.runFrom (I.A.run u₀) θ := by
    simp [hu, LDFA.run, LDFA.runFrom_append]
  have mortalCase (hm : I.Mortal (I.A.run u)) (hl : θ.length < Fintype.card SA) :
      I.HasMortalHole :=
    ⟨u, t, hh, hm, t₀.length, by simp [hj], by simpa [htail] using hl⟩
  rcases I.toTwoWordInstance.state_kinds hq with hm | hb | hthin
  · have hs := I.toTwoWordInstance.mortal_safe_word hm hc.1
    exact Or.inr (mortalCase (hend ▸ hs.2) hs.1)
  · exact Or.inl ⟨u₀, t₀, hp, Or.inl hb⟩
  · by_cases hv : I.Viable (I.A.run u)
    · obtain ⟨ξ, hξ⟩ := (I.viable_iff _).mp hv
      have hsafe := I.toTwoWordInstance.infiniteSafe_prepend hc.1 (hend ▸ hξ)
      exact Or.inl ⟨u₀, t₀, hp, Or.inr ⟨hthin, prepend θ ξ, hsafe,
        I.completes_survivorFree hc hg (prepend_prefix θ ξ)⟩⟩
    · have hm : I.Mortal (I.A.run u) := ⟨I.toTwoWordInstance.safeFrom_end hh.1.1, hv⟩
      exact Or.inr (mortalCase hm
        (I.toTwoWordInstance.thin_mortal_endpoint_short hthin hc.1 (hend ▸ hm)))

/-- Branching, thin survivor-free, or a short mortal tail. -/
theorem three_cases [Inhabited α] (hf : I.ForcedHeads) :
    I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole := by
  constructor
  · exact I.cases_of_hole hf
  · rintro (⟨u, t, hp, hb | ⟨_, ξ, hs, hf, hg⟩⟩ | ⟨u, t, hm⟩)
    · obtain ⟨θ, hc, hg, _⟩ := I.preHole_breaker hp hb
      exact ⟨u ++ θ, t ++ θ, I.preHole_complete hp hc hg⟩
    · exact I.hasHole_of_survivorFree hp hs hf hg
    · exact ⟨u, t, hm.1⟩

/-- A self survivor would make the stream purely periodic. -/
theorem aperiodic_selfSurvivorFree [Inhabited α] {t : Word α} {ξ : ℕ → α}
    (hn : ¬ ∃ p, 0 < p ∧ StreamPeriod ξ p) : I.SelfSurvivorFree t ξ := by
  intro i j he hsurv
  have ha := I.selfEvent_not_aligned he
  have ho : overhang t t i j ≠ [] := fun h => ha ((cross_aligned_iff he.2.1).mpr h)
  have hξ := (survives_iff_periodic he.2.1 ha ξ).mp hsurv
  exact hn ⟨(overhang t t i j).length, List.length_pos_iff.mpr ho,
    hξ ▸ periodicStream_period (overhang t t i j)⟩

/-- The maximum offset gives a uniform completion of both event families. -/
theorem lasso_completes [Inhabited α] {u t : Word α} {ξ : ℕ → α}
    (hl : I.Lasso (I.A.run u) ξ) (hf : I.SurvivorFree u t ξ)
    (hg : I.SelfSurvivorFree t ξ) :
    I.Completes u t (streamPrefix ξ (max u.length t.length + Fintype.card SA - 1)) ∧
      I.CompletesSelf t (streamPrefix ξ (max u.length t.length + Fintype.card SA - 1)) := by
  refine ⟨⟨I.toTwoWordInstance.infiniteSafe_prefix (I.toTwoWordInstance.lasso_safe hl) _, ?_⟩, ?_⟩
  · obtain ⟨α₀, l, hln, hlen, _, _, rfl⟩ := hl
    intro s e he hk
    apply lasso_breaking_prefix he.1 α₀ l hln (hf s e he)
    apply keeps_prefix hk
    apply streamPrefix_prefix
    have := cross_offset_le he.1
    have := le_max_left u.length t.length
    omega
  · obtain ⟨α₀, l, hln, hlen, _, _, rfl⟩ := hl
    intro i j he hk
    apply lasso_breaking_prefix he.2.1 α₀ l hln (hg i j he)
    apply keeps_prefix hk
    apply streamPrefix_prefix
    have := cross_offset_le he.2.1
    have := le_max_right u.length t.length
    omega

/-- Shorten the pre-hole while retaining the branching endpoint. -/
theorem short_branching_hole [Inhabited α] {u t : Word α} (hp : I.IsPreHole u t)
    (hb : I.Branching (I.A.run u)) :
    ∃ v w, I.IsHole v w ∧ v.length + w.length ≤
      4 * (12 * Fintype.card SA * Fintype.card SB * Fintype.card SC * Fintype.card SD) +
        6 * Fintype.card SA := by
  classical
  obtain ⟨v, w, hvw, he, hv, hw⟩ := I.toTwoWordInstance.short_preHole {I.A.run u} hp (by simp)
  have heq : I.A.run v = I.A.run u := Finset.mem_singleton.mp he
  obtain ⟨θ, hc, hg, hlen⟩ := I.preHole_breaker hvw (heq ▸ hb)
  refine ⟨v ++ θ, w ++ θ, I.preHole_complete hvw hc hg, ?_⟩
  simp only [List.length_append]
  omega

/-- Common lasso bound for a short pre-hole with both survivor conditions. -/
theorem short_hole_of_lasso [Inhabited α] {u t : Word α} {ξ : ℕ → α} {K : ℕ}
    (hp : I.IsPreHole u t) (hl : I.Lasso (I.A.run u) ξ)
    (hf : I.SurvivorFree u t ξ) (hg : I.SelfSurvivorFree t ξ)
    (hu : u.length < K) (ht : t.length < K) :
    ∃ v w, I.IsHole v w ∧ v.length + w.length ≤ 4 * K + 2 * Fintype.card SA := by
  let θ := streamPrefix ξ (max u.length t.length + Fintype.card SA - 1)
  obtain ⟨hc, hg⟩ := I.lasso_completes hl hf hg
  refine ⟨u ++ θ, t ++ θ, I.preHole_complete hp hc hg, ?_⟩
  simp only [List.length_append, θ, streamPrefix_length]
  omega

/-- Shortening may change self events, but none can survive. -/
theorem short_aperiodic_hole [Inhabited α] {u t : Word α} {ξ : ℕ → α}
    (hp : I.IsPreHole u t) (hl : I.Lasso (I.A.run u) ξ)
    (hn : ¬ ∃ p, 0 < p ∧ StreamPeriod ξ p) :
    ∃ v w, I.IsHole v w ∧ v.length + w.length ≤
      4 * (12 * Fintype.card SA * Fintype.card SB * Fintype.card SC * Fintype.card SD) +
        2 * Fintype.card SA := by
  classical
  obtain ⟨v, w, hvw, he, hv, hw⟩ := I.toTwoWordInstance.short_preHole {I.A.run u} hp (by simp)
  have heq : I.A.run v = I.A.run u := Finset.mem_singleton.mp he
  exact I.short_hole_of_lasso hvw (heq ▸ hl)
    (I.toTwoWordInstance.aperiodic_survivorFree hvw hn) (I.aperiodic_selfSurvivorFree hn) hv hw

end SelfTwoWordInstance

/-- The three-case decomposition for finite indexed state types. -/
theorem three_cases_self [Fintype α] [DecidableEq α] [Inhabited α] : ThreeCasesSelf α := by
  intro a b c d I hf
  exact I.three_cases hf

/-- The non-mortal bound follows from periodic shortening. -/
theorem nonMortalShortHoleBoundSelf_of_periodic [Fintype α] [DecidableEq α] [Inhabited α]
    (hper : ∀ a b c d, ∀ I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d),
      I.PurelyPeriodicShortPreHole (max (12 * a * b * c * d) (pumpCapacity a b c d))) :
    NonMortalShortHoleBoundSelf α pumpHoleBound := by
  intro a b c d I _ hcase
  obtain ⟨u, t, hp, hb | ⟨hthin, ξ, hs, hf, hg⟩⟩ := hcase
  · obtain ⟨v, w, hv, hlen⟩ := I.short_branching_hole hp hb
    refine ⟨v, w, hv, ?_⟩
    simp only [Fintype.card_fin] at hlen
    have hK := le_max_left (12 * a * b * c * d) (pumpCapacity a b c d)
    change v.length + w.length ≤ 4 * max _ _ + 6 * a
    omega
  · have hl := I.toTwoWordInstance.thin_lasso hthin hs
    by_cases hperiod : ∃ p, 0 < p ∧ StreamPeriod ξ p
    · obtain ⟨v, w, hp, he, hf, hg, hv, hw⟩ :=
        hper a b c d I (I.A.run u) ξ hthin hl hperiod ⟨u, t, hp, rfl, hf, hg⟩
      obtain ⟨v', w', hh, hlen⟩ := I.short_hole_of_lasso hp (he ▸ hl) hf hg hv hw
      refine ⟨v', w', hh, ?_⟩
      simp only [Fintype.card_fin] at hlen
      change v'.length + w'.length ≤ 4 * max _ _ + 6 * a
      omega
    · obtain ⟨v, w, hv, hlen⟩ := I.short_aperiodic_hole hp hl hperiod
      refine ⟨v, w, hv, ?_⟩
      simp only [Fintype.card_fin] at hlen
      have hK := le_max_left (12 * a * b * c * d) (pumpCapacity a b c d)
      change v.length + w.length ≤ 4 * max _ _ + 6 * a
      omega

end DeciENSSE.Core.Words.Self
