import DeciENSSE.Anchored.Desubstitution
import DeciNSSE.Holes.Agree

/-! # Agreement of positive channels

Agreement of two monitors on a support is extended to channels: the monitors agree, the
monitors carrying `F`, `R` and `S` as target and admissions agree, and `S'` and `Φ` are
preserved on the labels and letters of the support. The two monitors share their core type
but may have different alphabets. Such an agreement preserves positive holes over the
support, composes, and passes through derivation. It extends the agreement
`DeciNSSE.BoundedDepth.Agree` of `DeciNSSE/Holes/Agree.lean`, whose lemmas the proofs use.

## Main declarations

- `PosAgree`: agreement of monitors and channels on a support.
- `PosAgree.posHole_iff`: agreement preserves positive holes.
- `PosAgree.refl`, `PosAgree.comp`: identity and composition.
- `PosAgree.derive`: agreement passes through the derived monitors and channels.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth
variable {Γ Γ' Γ'' C : Type*}

/-- Agreement of monitors and channels on a support `E` under the letter map `φ`, possibly
into another alphabet. -/
structure PosAgree (D : Lettered Γ C) (D' : Lettered Γ' C) (P : PosChan Γ C)
    (P' : PosChan Γ' C) (φ : Γ → Γ') (E : List Γ) : Prop where
  /-- The monitors agree. -/
  neg : Agree D D' φ E
  /-- The monitors carrying `F`, `R` and `S` agree. -/
  pos : Agree (withPos D P) (withPos D' P') φ E
  /-- `S'` agrees on labels over the support. -/
  S' : ∀ L L', LabIn E L → LabIn E L' →
    (P'.S' (mapLab φ id L) (mapLab φ id L') ↔ P.S' L L')
  /-- `Φ` agrees on the letters of the support. -/
  Φ : ∀ a ∈ E, P'.Φ (φ a) ↔ P.Φ a

variable {D : Lettered Γ C} {D' : Lettered Γ' C} {P : PosChan Γ C} {P' : PosChan Γ' C}
  {φ : Γ → Γ'} {E : List Γ}

/-- Agreement preserves letter tests on words over the support. -/
theorem PosAgree.at_map (h : PosAgree D D' P P' φ E) {v : List Γ}
    (hv : ∀ a ∈ v, a ∈ E) (i : ℕ) : At P'.Φ (v.map φ) i ↔ At P.Φ v i := by
  simp only [At, List.getElem?_map]
  cases hi : v[i]? with
  | none => simp
  | some a => simp [h.Φ a (hv a (List.mem_of_getElem? hi))]

/-- Agreement preserves the positive condition of words over the support. -/
theorem PosAgree.pos_iff (h : PosAgree D D' P P' φ E) {v : List Γ}
    (hv : ∀ a ∈ v, a ∈ E) : Pos D' P' (v.map φ) ↔ Pos D P v := by
  have hl := h.neg.label_map hv
  have hu := labIn_label (E := E) D hv
  unfold Pos
  simp only [List.length_map, hl, h.neg.isComp_iff hv, h.at_map hv]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
  · have hU := hu v.length
    rcases he : D.label v v.length with _ | ⟨c, a⟩
    · simp
    · rw [he] at hU
      simp only [mapLab_some, exists_some_eq_iff]
      exact h.pos.tf a hU c
  · refine exists_congr fun x => exists_congr fun y => ?_
    rw [show P'.R (mapLab φ id (D.label v x)) (mapLab φ id (D.label v y)) ↔
      P.R (D.label v x) (D.label v y) from h.pos.Λ _ _ (hu x) (hu y)]
  · refine exists_congr fun x => and_congr_right fun _ => ?_
    exact h.pos.Λf _ _ (hu x) (hu _)
  · refine exists_congr fun x => and_congr_right fun _ => ?_
    exact and_congr (h.S' _ _ (hu x) (hu _)) Iff.rfl

/-- Agreement preserves positive holes over the support. -/
theorem PosAgree.posHole_iff (h : PosAgree D D' P P' φ E) {v : List Γ}
    (hv : ∀ a ∈ v, a ∈ E) : PosHole D' P' (v.map φ) ↔ PosHole D P v :=
  and_congr (h.neg.isHole_iff hv) (h.pos_iff hv)

/-- Every monitor and channel agree with themselves under the identity. -/
theorem PosAgree.refl (D : Lettered Γ C) (P : PosChan Γ C) (E : List Γ) :
    PosAgree D D P P id E where
  neg := Agree.refl _ _
  pos := Agree.refl _ _
  S' L L' _ _ := by rw [mapLab_id, mapLab_id]
  Φ _ _ := Iff.rfl

/-- Composition of agreements. -/
theorem PosAgree.comp {D'' : Lettered Γ'' C} {P'' : PosChan Γ'' C} {ψ : Γ → Γ'}
    {φ : Γ' → Γ''} (h₁ : PosAgree D D' P P' ψ E)
    (h₂ : PosAgree D' D'' P' P'' φ (E.map ψ)) : PosAgree D D'' P P'' (φ ∘ ψ) E where
  neg := h₁.neg.comp h₂.neg
  pos := h₁.pos.comp h₂.pos
  S' L L' hL hL' := by
    rw [mapLab_comp, mapLab_comp]
    exact (h₂.S' _ _ (hL.map ψ) (hL'.map ψ)).trans (h₁.S' _ _ hL hL')
  Φ a ha := (h₂.Φ _ (List.mem_map_of_mem ha)).trans (h₁.Φ a ha)

section Derive
variable (h : PosAgree D D' P P' φ E) {ℓ : Γ} (hℓ : ℓ ∈ E)
include h hℓ

/-- Agreement preserves letter tests in a block followed by the marker. -/
theorem PosAgree.at_block_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E) (p : ℕ) :
    At P'.Φ (X.map φ ++ [φ ℓ]) p ↔ At P.Φ (X ++ [ℓ]) p := by
  rw [show X.map φ ++ [φ ℓ] = (X ++ [ℓ]).map φ by simp]
  exact h.at_map (fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hX a ha
    · simpa using (List.mem_singleton.mp ha ▸ hℓ)) p

/-- Agreement preserves terminal events of blocks over the support. -/
theorem PosAgree.term_map {X : List Γ} (hX : ∀ a ∈ X, a ∈ E)
    (c : Option C) (d : C) :
    term D' P' (φ ℓ) c (X.map φ) d ↔ term D P ℓ c X d := by
  unfold term
  rw [List.length_map]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [h.neg.zlab_map hℓ hX]
  have hu := labIn_zlab hℓ D hX c p
  exact or_congr (h.pos.Λf _ (some (d, ℓ)) hu hℓ)
    (and_congr (h.S' _ (some (d, ℓ)) hu hℓ) (h.at_block_map hℓ hX p))

/-- Agreement passes through derivation, on every family of blocks over the support. -/
theorem PosAgree.derive (F : List (List Γ)) (hF : ∀ X ∈ F, ∀ a ∈ X, a ∈ E) :
    PosAgree (der D ℓ) (der D' (φ ℓ)) (posDer D P ℓ)
      (posDer D' P' (φ ℓ)) (List.map φ) F := by
  have hn := h.neg.derive hℓ F hF
  have hr := h.pos.derive hℓ F hF
  refine ⟨hn, ⟨hn.start, hn.inj, hn.κ, ?_, hr.Λ, ?_⟩, hr.Λ, ?_⟩
  · intro X hX c
    change P'.F (fcore D' (φ ℓ) c (X.map φ)) (φ ℓ) ∨
      term D' P' (φ ℓ) c (X.map φ) (fcore D' (φ ℓ) c (X.map φ)) ↔ _
    rw [h.neg.fcore_map hℓ (hF X hX), h.term_map hℓ (hF X hX)]
    exact or_congr (h.pos.tf ℓ hℓ _) Iff.rfl
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · change term D' P' (φ ℓ) c (X.map φ) (fcore D' (φ ℓ) c' (Y.map φ)) ↔ _
      rw [h.neg.fcore_map hℓ (hF Y hL'), h.term_map hℓ (hF X hL)]
      rfl
  · intro X hX
    exact h.at_block_map hℓ (hF X hX) 0

end Derive

end DeciENSSE.Anchored
