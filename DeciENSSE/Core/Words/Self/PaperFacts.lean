import DeciENSSE.Core.Words.Self.Bound

/-! # Deletion, counting and the three cases for holes with self events

Statements of the non-mortal case analysis in the form of the paper (`app:nm`), for
instances with self events: the deletion lemma for good pairs (`lem:nm-deletion`), the
counting lemma behind the pump (`lem:nm-count`), the thin and mortal alternatives after a
completion, the three cases at every alphabet, including the empty one
(`thm:nm-three-cases`), and the aligned pairs of extended words (`lem:nm-hit`).

## Main declarations

- `SelfTwoWordInstance.delete_good`: deleting loops preserves good pairs.
- `SelfTwoWordInstance.partnered`, `SelfTwoWordInstance.unpartnered`,
  `SelfTwoWordInstance.count_short`: rest cuts and the counting lemma.
- `SelfTwoWordInstance.thin_completion_stream`, `SelfTwoWordInstance.completion_mortal`,
  `SelfTwoWordInstance.three_cases_total`: the three cases.
- `aligned_empty`, `aligned_snoc`: aligned pairs under extension.
-/
namespace DeciENSSE.Core.Words.Self.SelfTwoWordInstance
open TwoWordInstance DeciNSSE.RejectedTail
variable {α SA SB SA' SB' : Type*}
variable [Fintype SA] [Fintype SB] [Fintype SA'] [Fintype SB']
variable [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB']
variable (I : SelfTwoWordInstance α SA SB SA' SB')

/-- Deleting loops preserves good pairs when the five deep/shallow matched-pair
implications hold and one head survives. These implications are the cases of
lifting matched pairs through the deletion image; wholly shallow pairs lift automatically. -/
theorem delete_good {ξ : ℕ → α} {x w y x' w' y' : Word α}
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
  refine ⟨⟨I.toTwoWordInstance.pumpGood_delete hg.1 hA hA' hB hB' hDD hDS hSD hhead,
    I.selfGuardFree_delete hg.2 hB hSS hS⟩, (I.A.run_delete y hA).symm, ?_⟩
  simp only [List.length_append]
  rcases hpos with h | h <;> have := List.length_pos_iff.mpr h <;> omega

/-- The finite set of partnered rest cuts. -/
noncomputable def partnered (ξ : ℕ → α) (u t : Word α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun j => ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ)

/-- The finite set of unpartnered rest cuts. -/
noncomputable def unpartnered (ξ : ℕ → α) (u t : Word α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun j => ¬ ∃ e ≤ t.length, prepend (u.drop j) ξ = prepend (t.drop e) ξ)

/-- If all four deletion conditions fail, both words are strictly below the pump bound. -/
theorem count_short {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p)
    {u t : Word α} {ru rt : ℕ} (hg : I.PumpGood ξ u t)
    (hu : PeriodicSplit ξ p u ru) (ht : PeriodicSplit ξ p t rt)
    (h1 : u.length - ru < t.length - rt + Fintype.card (SA × SA' × Fin p))
    (h2 : (partnered ξ u t ru).card ≤ Fintype.card (SA × SA' × SB × SB' × Bool))
    (h3 : (unpartnered ξ u t ru).card ≤ Fintype.card (SA × SA'))
    (h4 : (unpartnered ξ t u rt).card ≤ Fintype.card (SB × SB')) :
    u.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p ∧
    t.length < pumpBound (Fintype.card SA) (Fintype.card SB) (Fintype.card SA') (Fintype.card SB') p := by
  classical
  have hul := hu.le_length
  have htl := ht.le_length
  have hend := I.toTwoWordInstance.periodicEnd_lt hp ht hg.1.2.1 hg.1.2.2.1
  have hru : (partnered ξ u t ru).card + (unpartnered ξ u t ru).card = ru := by
    simp only [partnered, unpartnered, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hrt : (partnered ξ t u rt).card + (unpartnered ξ t u rt).card = rt := by
    simp only [partnered, unpartnered, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hPtu : (partnered ξ t u rt).card ≤ (partnered ξ u t ru).card := by
    apply Finset.card_le_card_of_injOn (fun e => ru - (rt - e))
    · intro e he
      simp only [Finset.mem_coe, partnered, Finset.mem_filter, Finset.mem_range] at he
      obtain ⟨her, s, hs, heq⟩ := he
      obtain ⟨hsr, hrl⟩ := partner_eq_t hu ht her hs heq
      simp only [Finset.mem_coe, partnered, Finset.mem_filter, Finset.mem_range]
      rw [show ru - (rt - e) = s by omega]
      exact ⟨hsr, e, by omega, heq.symm⟩
    · intro e₁ he₁ e₂ he₂ heq
      simp only [Finset.mem_coe, partnered, Finset.mem_filter, Finset.mem_range] at he₁ he₂
      obtain ⟨her₁, s₁, hs₁, heq₁⟩ := he₁
      obtain ⟨her₂, s₂, hs₂, heq₂⟩ := he₂
      have := partner_eq_t hu ht her₁ hs₁ heq₁
      have := partner_eq_t hu ht her₂ hs₂ heq₂
      simp only at heq
      omega
  rw [pumpBound_card]
  omega

/-- A thin pre-hole completion ending in a non-mortal state extends to a
survivor-free safe stream with exactly the prescribed finite prefix. -/
theorem thin_completion_stream {u t θ : Word α} (_hp : I.IsPreHole u t)
    (hc : I.Completes u t θ) (hg : I.CompletesSelf t θ)
    (hn : ¬ I.Mortal (I.A.run (u ++ θ))) :
    ∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ ∧
      I.SelfSurvivorFree t ξ ∧ streamPrefix ξ θ.length = θ := by
  classical
  have hend : I.A.run (u ++ θ) = I.A.runFrom (I.A.run u) θ := by
    simp [LDFA.run, LDFA.runFrom_append]
  have hs := I.toTwoWordInstance.safeFrom_end hc.1
  have hv : I.Viable (I.A.runFrom (I.A.run u) θ) := by
    by_contra h
    exact hn (hend ▸ ⟨hs, h⟩)
  obtain ⟨ξ, hξ⟩ := (I.viable_iff _).mp hv
  have hsafe := I.toTwoWordInstance.infiniteSafe_prepend hc.1 hξ
  exact ⟨prepend θ ξ, hsafe, (I.completes_survivorFree hc hg (prepend_prefix θ ξ)).1,
    (I.completes_survivorFree hc hg (prepend_prefix θ ξ)).2, prepend_prefix θ ξ⟩

/-- The original completed hole is mortal whenever its pre-hole endpoint is
not branching and the thin/non-mortal alternative fails. -/
theorem completion_mortal {u t θ : Word α} (hp : I.IsPreHole u t)
    (hc : I.Completes u t θ) (hg : I.CompletesSelf t θ)
    (hb : ¬ I.Branching (I.A.run u))
    (hn : ¬ (I.Thin (I.A.run u) ∧ ¬ I.Mortal (I.A.run (u ++ θ)))) :
    I.IsMortalHole (u ++ θ) (t ++ θ) := by
  classical
  have hend : I.A.run (u ++ θ) = I.A.runFrom (I.A.run u) θ := by
    simp [LDFA.run, LDFA.runFrom_append]
  have hq := I.toTwoWordInstance.safeFrom_end hp.1
  have hm : I.Mortal (I.A.run (u ++ θ)) ∧ θ.length < Fintype.card SA := by
    rcases I.toTwoWordInstance.state_kinds hq with hm | hbranch | hthin
    · have h := I.toTwoWordInstance.mortal_safe_word hm hc.1
      exact ⟨hend ▸ h.2, h.1⟩
    · exact (hb hbranch).elim
    · have h : I.Mortal (I.A.run (u ++ θ)) := by tauto
      exact ⟨h, I.toTwoWordInstance.thin_mortal_endpoint_short hthin hc.1 (hend ▸ h)⟩
  refine ⟨I.preHole_complete hp hc hg, hm.1, t.length, ?_, ?_⟩
  · simp [I.toTwoWordInstance.J_append hp.2.1 θ]
  · simpa using hm.2

/-- Three cases, including the empty alphabet. -/
theorem three_cases_total (hf : I.ForcedHeads) :
    I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole := by
  classical
  cases isEmpty_or_nonempty α with
  | inl h =>
    refine ⟨I.cases_of_hole hf, ?_⟩
    rintro (⟨u, t, hp, hb | ⟨ht, ξ, hs⟩⟩ | ⟨u, t, hm⟩)
    · obtain ⟨_, r, _, _, x, _⟩ := hb
      exact isEmptyElim x
    · exact isEmptyElim (ξ 0)
    · exact ⟨u, t, hm.1⟩
  | inr h =>
    let := Classical.inhabited_of_nonempty h
    exact I.three_cases hf
end DeciENSSE.Core.Words.Self.SelfTwoWordInstance

namespace DeciENSSE.Core.Words
open TwoWordInstance
variable {α : Type*}

/-- The unique aligned pair when one word is empty. -/
theorem aligned_empty (u t : Word α) (s e : ℕ) :
    (Aligned u [] s e ↔ s = u.length ∧ e = 0) ∧
    (Aligned [] t s e ↔ s = 0 ∧ e = t.length) := by
  simp only [Aligned, List.length_nil, Nat.le_zero, List.drop_nil,
    List.drop_eq_nil_iff, eq_comm (a := ([] : List α))]
  constructor <;> constructor
  · rintro ⟨hs, he, hl⟩; exact ⟨by omega, he⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨le_rfl, rfl, le_rfl⟩
  · rintro ⟨hs, he, hl⟩; exact ⟨hs, by omega⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, le_rfl, le_rfl⟩

/-- Appending letters either gives the final aligned pair or preserves an old pair. -/
theorem aligned_snoc (u t : Word α) (c d : α) (s e : ℕ) :
    Aligned (u ++ [c]) (t ++ [d]) s e ↔
      (s = u.length + 1 ∧ e = t.length + 1) ∨ (c = d ∧ Aligned u t s e) := by
  constructor
  · rintro ⟨hs, he, hd⟩
    have hlen := congrArg List.length hd
    simp only [List.length_drop, List.length_append, List.length_singleton] at hs he hlen
    by_cases hsu : s ≤ u.length
    · have het : e ≤ t.length := by omega
      rw [List.drop_append_of_le_length hsu, List.drop_append_of_le_length het] at hd
      have hlast : c = d := by
        have hh := congrArg List.getLast? hd
        simpa using hh
      subst d
      exact Or.inr ⟨rfl, hsu, het, List.append_cancel_right hd⟩
    · exact Or.inl ⟨by omega, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hs, he, hd⟩)
    · simp [Aligned]
    · refine ⟨by simp; omega, by simp; omega, ?_⟩
      simp only [List.drop_append_of_le_length hs, List.drop_append_of_le_length he, hd]
end DeciENSSE.Core.Words
