import DeciENSSE.Core.Words.Self.Basic
import DeciENSSE.Core.Words.Pump

/-! # Pumping with target self guards

The six periodic deletion cases also preserve self-survivor freeness and
the spine endpoint, with the same polynomial capacity.

## Main declarations

- `SelfTwoWordInstance.selfGuardFree_delete`
- `SelfTwoWordInstance.pumpGood_short`
- `purelyPeriodicShortPreHole_capacity`
-/

namespace DeciENSSE.Core.Words.Self.SelfTwoWordInstance

variable {α : Type*}
open DeciENSSE.Core.Words.TwoWordInstance

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SelfTwoWordInstance α SA SB SA' SB')

/-- No strict target pair with equal infinite suffixes is self-guarded. -/
def SelfGuardFree (ξ : ℕ → α) (t : Word α) : Prop :=
  ∀ i j, i < j → j ≤ t.length →
    prepend (t.drop i) ξ = prepend (t.drop j) ξ →
      (I.B.atCut t i, I.B.atCut t j) ∉ I.SelfGuard

/-- Self-survivor freeness is exclusion of guarded equal periodic suffixes. -/
theorem selfSurvivorFree_iff [Inhabited α] {t : Word α} {ξ : ℕ → α}
    (hj : I.J t = some t.length) : I.SelfSurvivorFree t ξ ↔ I.SelfGuardFree ξ t := by
  constructor
  · intro hf i j hij hjt heq hguard
    obtain ⟨hc, hs⟩ := (survives_iff_prepend_eq (by omega : i ≤ t.length)
      hjt (by omega) ξ).mpr heq
    exact hf i j ⟨hij, hc, ⟨t.length, hj, hjt⟩, hguard⟩ hs
  · intro hf i j he hs
    have hij := he.1
    exact hf i j he.1 he.2.1.2.1
      ((survives_iff_prepend_eq he.2.1.1 he.2.1.2.1 (by omega) ξ).mp
        ⟨he.2.1, hs⟩) he.2.2.2

/-- The `TwoWordInstance.PumpGood` invariant, strengthened by self-freeness. -/
def PumpGood (ξ : ℕ → α) (u t : Word α) : Prop :=
  I.toTwoWordInstance.PumpGood ξ u t ∧ I.SelfGuardFree ξ t

/-- The self-aware pumping invariant retains both survivor conditions. -/
theorem pumpGood_iff [Inhabited α] (ξ : ℕ → α) (u t : Word α) :
    I.PumpGood ξ u t ↔
      I.IsPreHole u t ∧ I.SurvivorFree u t ξ ∧ I.SelfSurvivorFree t ξ := by
  constructor
  · rintro ⟨hg, hs⟩
    obtain ⟨hp, hf⟩ := (I.toTwoWordInstance.pumpGood_iff ξ u t).mp hg
    exact ⟨hp, hf, (I.selfSurvivorFree_iff hp.2.1).mpr hs⟩
  · rintro ⟨hp, hf, hs⟩
    exact ⟨(I.toTwoWordInstance.pumpGood_iff ξ u t).mpr ⟨hp, hf⟩,
      (I.selfSurvivorFree_iff hp.2.1).mp hs⟩

/-- The retained-cut map preserves strict order, states, and equal suffixes. -/
theorem selfGuardFree_delete {ξ : ℕ → α} {x' w' y' : Word α}
    (hg : I.SelfGuardFree ξ (x' ++ w' ++ y'))
    (hB : I.B.runFrom (I.B.run x') w' = I.B.run x')
    (hDD : ∀ e₁ e₂, e₁ < e₂ → e₂ < x'.length →
      prepend (x'.drop e₁ ++ y') ξ = prepend (x'.drop e₂ ++ y') ξ →
      prepend (x'.drop e₁ ++ w' ++ y') ξ = prepend (x'.drop e₂ ++ w' ++ y') ξ)
    (hDS : ∀ e < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop e ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop e ++ w' ++ y') ξ = prepend (y'.drop k) ξ) :
    I.SelfGuardFree ξ (x' ++ y') := by
  intro i j hij hj hsuf hgd
  simp only [List.length_append] at hj
  by_cases hjx : j < x'.length
  · have hix : i ≤ x'.length := by omega
    rw [List.drop_append_of_le_length hix,
      List.drop_append_of_le_length hjx.le] at hsuf
    apply hg i j hij (by simp; omega)
      (by rw [drop_delete_left w' y' hix, drop_delete_left w' y' hjx.le]
          exact hDD i j hij hjx hsuf)
    rwa [I.B.atCut_delete_left w' y' hix, I.B.atCut_delete_left w' y' hjx.le]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hjx)
    by_cases hix : i < x'.length
    · rw [List.drop_append_of_le_length hix.le, List.drop_length_add_append] at hsuf
      apply hg i (x'.length + w'.length + k) (by omega) (by simp; omega)
        (by rw [drop_delete_left w' y' hix.le, drop_delete_right]
            exact hDS i hix k (by omega) hsuf)
      rwa [I.B.atCut_delete_left w' y' hix.le, I.B.atCut_delete y' hB k]
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hix)
      rw [List.drop_length_add_append, List.drop_length_add_append] at hsuf
      apply hg (x'.length + w'.length + l) (x'.length + w'.length + k)
        (by omega) (by simp; omega)
        (by rw [drop_delete_right, drop_delete_right]; exact hsuf)
      rwa [I.B.atCut_delete y' hB l, I.B.atCut_delete y' hB k]

/-- An absorbed factor lifts both kinds of deep self comparison. -/
theorem self_delete_absorbed {ξ : ℕ → α} {w' y' : Word α}
    (hW' : prepend w' (prepend y' ξ) = prepend y' ξ) (x' : Word α) :
    (∀ e₁ e₂, e₁ < e₂ → e₂ < x'.length →
      prepend (x'.drop e₁ ++ y') ξ = prepend (x'.drop e₂ ++ y') ξ →
      prepend (x'.drop e₁ ++ w' ++ y') ξ = prepend (x'.drop e₂ ++ w' ++ y') ξ) ∧
    (∀ e < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop e ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop e ++ w' ++ y') ξ = prepend (y'.drop k) ξ) := by
  constructor
  · intro e₁ e₂ _ _ h; simpa only [prepend_mid hW'] using h
  · intro e _ k _ h; simpa only [prepend_mid hW'] using h

/-- Both deep comparison premises contradict non-self-similarity. -/
theorem self_delete_rest {ξ : ℕ → α} {y' : Word α}
    (hX : NonSelfSimilar (prepend y' ξ)) (x' w' : Word α) :
    (∀ e₁ e₂, e₁ < e₂ → e₂ < x'.length →
      prepend (x'.drop e₁ ++ y') ξ = prepend (x'.drop e₂ ++ y') ξ →
      prepend (x'.drop e₁ ++ w' ++ y') ξ = prepend (x'.drop e₂ ++ w' ++ y') ξ) ∧
    (∀ e < x'.length, ∀ k ≤ y'.length,
      prepend (x'.drop e ++ y') ξ = prepend (y'.drop k) ξ →
      prepend (x'.drop e ++ w' ++ y') ξ = prepend (y'.drop k) ξ) := by
  constructor
  · intro e₁ e₂ hlt he h
    rw [prepend_assoc, prepend_assoc] at h
    have hl := congrArg List.length (hX.prepend_inj h)
    simp only [List.length_drop] at hl
    omega
  · intro e he k hk h
    exfalso
    rw [prepend_assoc, ← prepend_shift _ ξ hk] at h
    exact hX.ne_shift (List.ne_nil_of_length_pos (by simp; omega)) k h

/-- Deletion with the absorbed-factor discharger. -/
theorem selfGuardFree_delete_absorbed {ξ : ℕ → α} {x' w' y' : Word α}
    (hg : I.SelfGuardFree ξ (x' ++ w' ++ y'))
    (hB : I.B.runFrom (I.B.run x') w' = I.B.run x')
    (hW' : prepend w' (prepend y' ξ) = prepend y' ξ) :
    I.SelfGuardFree ξ (x' ++ y') :=
  I.selfGuardFree_delete hg hB (self_delete_absorbed hW' x').1
    (self_delete_absorbed hW' x').2

/-- Deletion with the non-self-similar rest discharger. -/
theorem selfGuardFree_delete_rest {ξ : ℕ → α} {x' w' y' : Word α}
    (hg : I.SelfGuardFree ξ (x' ++ w' ++ y'))
    (hB : I.B.runFrom (I.B.run x') w' = I.B.run x')
    (hX : NonSelfSimilar (prepend y' ξ)) :
    I.SelfGuardFree ξ (x' ++ y') :=
  I.selfGuardFree_delete hg hB (self_delete_rest hX x' w').1
    (self_delete_rest hX x' w').2

/-- One deletion preserves both survivor conditions and the spine endpoint. -/
def Shrinks (ξ : ℕ → α) (u t : Word α) : Prop :=
  ∃ u' t', I.PumpGood ξ u' t' ∧ I.A.run u' = I.A.run u ∧
    u'.length + t'.length < u.length + t.length

/-- Parent deletion with a proof of self-freeness for its concrete output. -/
theorem shrink_of_delete {ξ : ℕ → α} {u t x w y x' w' y' : Word α}
    (hu : x ++ w ++ y = u) (ht : x' ++ w' ++ y' = t) (hpos : w ≠ [] ∨ w' ≠ [])
    (hself : I.SelfGuardFree ξ (x' ++ y'))
    (hg : I.toTwoWordInstance.PumpGood ξ u t)
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
  refine ⟨x ++ y, x' ++ y', ⟨I.toTwoWordInstance.pumpGood_delete hg hA hA' hB hB' hDD hDS hSD
    hhead, hself⟩,
    (I.A.run_delete y hA).symm, ?_⟩
  simp only [List.length_append]
  rcases hpos with h | h
  · have := List.length_pos_iff.mpr h; omega
  · have := List.length_pos_iff.mpr h; omega

variable {ξ : ℕ → α} {p : ℕ}

/-- Joint deletion in the periodic ends preserves the self-aware invariant. -/
theorem shrink_joint (hp : LeastStreamPeriod ξ p) {u t : Word α} {ru rt : ℕ}
    (hg : I.PumpGood ξ u t) (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ u.length - ru)
    (h' : Fintype.card (SA × SA' × SB × SB' × Fin p × Bool) ≤ t.length - rt) :
    I.Shrinks ξ u t := by
  obtain ⟨hg, hself⟩ := hg
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
  refine I.shrink_of_delete hu' ht' (Or.inl (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · apply I.selfGuardFree_delete_absorbed (by rwa [ht'])
    · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB.symm
    · exact hW'
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
  obtain ⟨hg, hself⟩ := hg
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
  refine I.shrink_of_delete (x' := []) (w' := []) (y' := t) hu' (by simp)
    (Or.inl (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hself
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
  obtain ⟨hg, hself⟩ := hg
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
  refine I.shrink_of_delete (x := []) (w := []) (y := u) (by simp) ht'
    (Or.inr (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply I.selfGuardFree_delete_absorbed (by rwa [ht'])
    · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB.symm
    · exact hW'
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
  obtain ⟨hg, hself⟩ := hg
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
  refine I.shrink_of_delete hu' ht' (Or.inl (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · apply I.selfGuardFree_delete_rest (by rwa [ht'])
    · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hfB
    · rw [← hU₂]; exact hX
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
  obtain ⟨hg, hself⟩ := hg
  have hul := hu.le_length
  obtain ⟨i, hi, j, hj, hlt, hf⟩ := exists_lt_map_eq_finset P
    (fun j => (I.A.atCut u j, I.A'.atCut u j)) h
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hjr, hun⟩ := hP j hj
  obtain ⟨x, w, hu', hxl, hwl⟩ := exists_split3 u hlt.le (by omega : j ≤ u.length)
  refine I.shrink_of_delete (x' := []) (w' := []) (y' := t) hu' (by simp)
    (Or.inl (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hself
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
  obtain ⟨hg, hself⟩ := hg
  have htl := ht.le_length
  obtain ⟨i, hi, j, hj, hlt, hf⟩ := exists_lt_map_eq_finset P
    (fun e => (I.B.atCut t e, I.B'.atCut t e)) h
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hjr, hun⟩ := hP j hj
  obtain ⟨x', w', ht', hxl', hwl'⟩ := exists_split3 t hlt.le (by omega : j ≤ t.length)
  refine I.shrink_of_delete (x := []) (w := []) (y := u) (by simp) ht'
    (Or.inr (List.ne_nil_of_length_pos (by omega))) ?_ hg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply I.selfGuardFree_delete_rest (by rwa [ht'])
    · exact I.B.runFrom_of_atCut ht' hxl' (by omega) hf.1
    · exact nonSelfSimilar_of_rest hp ht hjr
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

/-- Self guards preserve the polynomial capacity of the deletion toolkit. -/
theorem purelyPeriodicShortPreHole_pump [Inhabited α] :
    I.PurelyPeriodicShortPreHole
      (pumpCapacity (Fintype.card SA) (Fintype.card SB) (Fintype.card SA')
        (Fintype.card SB')) := by
  rintro q ξ - hl hper ⟨u, t, hph, hq, hsf, hself⟩
  obtain ⟨p, hp⟩ := leastPeriod_exists hper
  have hpa := I.toTwoWordInstance.lasso_leastPeriod_le hl hp
  obtain ⟨u', t', hg, hrun, hu', ht'⟩ :=
    I.pumpGood_short hp (TwoWordInstance.pumpSize_le hpa) _ u t le_rfl
      ((I.pumpGood_iff ξ u t).mpr ⟨hph, hsf, hself⟩)
  obtain ⟨hph', hsf', hself'⟩ := (I.pumpGood_iff ξ u' t').mp hg
  exact ⟨u', t', hph', hrun.trans hq, hsf', hself', hu', ht'⟩

end DeciENSSE.Core.Words.Self.SelfTwoWordInstance

namespace DeciENSSE.Core.Words.Self

variable {α : Type*}

/-- The periodic shortening premise with the maximum-form capacity. -/
theorem purelyPeriodicShortPreHole_capacity [Inhabited α] (a b c d : ℕ)
    (I : SelfTwoWordInstance α (Fin a) (Fin b) (Fin c) (Fin d)) :
    I.PurelyPeriodicShortPreHole (max (12 * a * b * c * d) (pumpCapacity a b c d)) := by
  have h := I.purelyPeriodicShortPreHole_pump
  simp only [Fintype.card_fin] at h
  intro q ξ hq hl hper hex
  obtain ⟨u, t, h1, h2, h3, h4, h5, h6⟩ := h q ξ hq hl hper hex
  exact ⟨u, t, h1, h2, h3, h4,
    h5.trans_le (le_max_right _ _), h6.trans_le (le_max_right _ _)⟩

end DeciENSSE.Core.Words.Self

