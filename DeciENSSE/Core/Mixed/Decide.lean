import DeciENSSE.Core.Mixed.Extract
import DeciENSSE.Core.Mixed.CondI
import DeciENSSE.Core.Mixed.Units

/-! # Conditional decision of n-ary mixed existential entailment

Combine satisfiability, unit conditions, and a finite self-aware hole search.
The only mathematical premise is a uniform short-hole bound.

## Main declarations

- `SS2Self.BoundedHoleS`, `SS2Self.decideBoundedHoleS`,
  `BoundedEntailsMixed`, `boundedCheckMixed`, `existsEntailsT_iff_boundedS`,
  `decideExistsEntailsAnyOfShortHoles`.
-/

set_option autoImplicit false

namespace DeciENSSE.Core

namespace SS2Self
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- Finite enumeration of two words over a finite alphabet with total length at most L. -/
def BoundedHoleS (I : SS2Self α SA SB SC SD) (L : ℕ) : Prop :=
  ∃ n : Fin (L + 1), ∃ m : Fin (L + 1), n.val + m.val ≤ L ∧
    ∃ u : Fin n.val → α, ∃ t : Fin m.val → α,
      I.IsHoleS (List.ofFn u) (List.ofFn t)

/-- Finite word enumeration decides bounded hole existence. -/
instance instDecidableBoundedHoleS (I : SS2Self α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHoleS L) := by
  unfold BoundedHoleS
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Finite tuple enumeration is equivalent to a total word-length bound. -/
theorem boundedHoleS_iff (I : SS2Self α SA SB SC SD) (L : ℕ) :
    I.BoundedHoleS L ↔ ∃ u t, I.IsHoleS u t ∧ u.length + t.length ≤ L := by
  constructor
  · rintro ⟨n, m, hlen, u, t, hh⟩
    exact ⟨List.ofFn u, List.ofFn t, hh, by simpa using hlen⟩
  · rintro ⟨u, t, hh, hlen⟩
    refine ⟨⟨u.length, by omega⟩, ⟨t.length, by omega⟩, hlen,
      (fun i => u[i]), (fun i => t[i]), ?_⟩
    simpa using hh

/-- Computable Fin transport, including both coordinates of the self guard. Truncated equivalences
eliminate into the subsingleton `Decidable P`. -/
def decideBoundedHoleS (I : SS2Self α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHoleS L) :=
  (Fintype.truncEquivFin SA).recOnSubsingleton fun a =>
  (Fintype.truncEquivFin SB).recOnSubsingleton fun b =>
  (Fintype.truncEquivFin SC).recOnSubsingleton fun c =>
  (Fintype.truncEquivFin SD).recOnSubsingleton fun d =>
    decidable_of_iff ((I.rename a b c d).BoundedHoleS L) (by
      rw [boundedHoleS_iff, boundedHoleS_iff, rename_boundedHoleS])

/-- The universal bound is used only to complete the bounded hole search. -/
theorem hasHoleS_iff_bounded (I : SS2Self α SA SB SC SD) (B : HoleBound)
    (hB : ShortHoleBoundS α B) (hfh : I.FH) :
    I.HasHoleS ↔ I.BoundedHoleS
      (B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD)) := by
  rw [boundedHoleS_iff]
  exact ⟨shortHoleBoundS_transport I B hB hfh,
    fun ⟨u, t, hh, _⟩ => ⟨u, t, hh⟩⟩
end SS2Self

namespace Mixed
open DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Exact extraction sizes, including the sticky flag and consequent upper summary in the target
state. -/
def extractedBoundS (B : HoleBound) (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  B (Fintype.card (Finset (X × Bool))) (Fintype.card (TargetState X Z))
    (Fintype.card (Finset ((X ⊕ Z) × Bool)))
    (Fintype.card (Finset ((X ⊕ Z) × Bool)))

/-- Specification of the finite procedure. Satisfiability, I0 and U use their finite deciders; the
remaining quantifiers enumerate signed visible variables and pairs of bounded words over Fin
n. -/
def BoundedEntailsMixed (B : HoleBound) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  (¬ ∃ ρ, SatT c ρ φ) ∨ ((∃ ρ, SatT c ρ ψ) ∧ CondI0 c φ ψ ∧ CondU c φ ψ ∧
    ∀ p q, ¬ (extractS c φ ψ p q).BoundedHoleS (extractedBoundS B X Z))

/-- Dispatch in the order satisfiability, I0, U, bounded signed holes. The antecedent witness
required by `decideCondU` comes from the first test. -/
def decideBoundedEntailsMixed (B : HoleBound) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (BoundedEntailsMixed B c φ ψ) := by
  letI := decideSatMixed c φ
  if hφ : ∃ ρ, SatT c ρ φ then
    letI := decideSatMixed c ψ
    if hψ : ∃ ρ, SatT c ρ ψ then
      letI := decideCondI0 c φ ψ
      if hi : CondI0 c φ ψ then
        letI := decideCondU c φ ψ hφ
        if hu : CondU c φ ψ then
          letI (p q : X × Bool) := SS2Self.decideBoundedHoleS (extractS c φ ψ p q)
            (extractedBoundS B X Z)
          exact decidable_of_iff
            (∀ p q, ¬ (extractS c φ ψ p q).BoundedHoleS (extractedBoundS B X Z))
            (by simp [BoundedEntailsMixed, hφ, hψ, hi, hu])
        else
          exact isFalse (by simp [BoundedEntailsMixed, hφ, hu])
      else
        exact isFalse (by simp [BoundedEntailsMixed, hφ, hi])
    else
      exact isFalse (by simp [BoundedEntailsMixed, hφ, hψ])
  else
    exact isTrue (Or.inl hφ)

/-- Executable finite Boolean check, defined even for an unproved bound. -/
def boundedCheckMixed (B : HoleBound) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Bool :=
  @decide (BoundedEntailsMixed B c φ ψ) (decideBoundedEntailsMixed B c φ ψ)

/-- The Boolean check agrees with its finite specification. -/
theorem boundedCheckMixed_eq_true (B : HoleBound) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    boundedCheckMixed B c φ ψ = true ↔ BoundedEntailsMixed B c φ ψ :=
  @decide_eq_true_iff _ (decideBoundedEntailsMixed B c φ ψ)

/-- Even an unproved bound gives a sound negative result. -/
theorem boundedEntailsMixed_of_entails (B : HoleBound) {c : Fin n → Bool}
    {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (he : ExistsEntailsT c φ ψ) : BoundedEntailsMixed B c φ ψ := by
  classical
  by_cases hφ : ∃ ρ, SatT c ρ φ
  · have hψ : ∃ ρ, SatT c ρ ψ := by
      obtain ⟨ρ, hρ⟩ := hφ
      obtain ⟨σ, _, hσ⟩ := he ρ (fun _ => trivial) hρ
      exact ⟨_, hσ⟩
    obtain ⟨hi, hu, hh⟩ := (mixed_reduction hφ hψ).mp he
    refine Or.inr ⟨hψ, hi, hu, fun p q hb => ?_⟩
    obtain ⟨u, t, ht, _⟩ := (SS2Self.boundedHoleS_iff _ _).mp hb
    exact hh p q ⟨u, t, ht⟩
  · exact Or.inl hφ

/-- Correctness using the unconditional finite-head theorem of extraction. -/
theorem existsEntailsT_iff_boundedS (B : HoleBound) (hB : ShortHoleBoundS (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ BoundedEntailsMixed B c φ ψ := by
  classical
  refine ⟨boundedEntailsMixed_of_entails B, ?_⟩
  rintro (hφ | ⟨hψ, hi, hu, hh⟩)
  · exact existsEntailsT_of_unsat hφ
  · by_cases hφ : ∃ ρ, SatT c ρ φ
    · apply (mixed_reduction hφ hψ).mpr
      exact ⟨hi, hu, fun p q h => hh p q
        ((SS2Self.hasHoleS_iff_bounded _ B hB (extractS_fh p q)).mp h)⟩
    · exact existsEntailsT_of_unsat hφ

/-- A uniform short-hole bound makes the Boolean check exact. -/
theorem existsEntails_iff_boundedCheckMixed (B : HoleBound) (hB : ShortHoleBoundS (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ boundedCheckMixed B c φ ψ = true :=
  (existsEntailsT_iff_boundedS B hB c φ ψ).trans
    (boundedCheckMixed_eq_true B c φ ψ).symm

/-- Arbitrary-tree existential entailment, for every variance and finite visible/hidden carriers.
The bound proof is the only mathematical premise. -/
def decideExistsEntailsAnyOfShortHoles (B : HoleBound) (hB : ShortHoleBoundS (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsT c φ ψ) := by
  letI := decideBoundedEntailsMixed B c φ ψ
  exact decidable_of_iff (BoundedEntailsMixed B c φ ψ)
    (existsEntailsT_iff_boundedS B hB c φ ψ).symm

/-- The conditional decision agrees with existential entailment. -/
theorem decideExistsEntailsAnyOfShortHoles_correct (B : HoleBound) (hB : ShortHoleBoundS (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide (ExistsEntailsT c φ ψ) (decideExistsEntailsAnyOfShortHoles B hB c φ ψ) = true ↔
      ExistsEntailsT c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyOfShortHoles B hB c φ ψ)

namespace DecideMixedExamples
open LeafHornExamples ConditionsExamples

/-- A positive mixed input with no joint parity, for every candidate bound. Semantic correctness
avoids evaluating the enormous condition searches. -/
theorem mixed_positive (B : HoleBound) :
    (¬ ∃ s : Bool ⊕ Unit → Bool,
      (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
      (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i))) ∧
    boundedCheckMixed B arrow mixed embedded = true :=
  ⟨embedded_no_joint_parity, (boundedCheckMixed_eq_true B arrow mixed embedded).mpr
    (boundedEntailsMixed_of_entails B embedded_entails)⟩

/-- The same consequent fails for the empty antecedent, without joint parity. -/
theorem mixed_negative (B : HoleBound) (hB : ShortHoleBoundS (Fin 3) B) :
    (¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
    boundedCheckMixed B arrow [] embedded = false := by
  refine ⟨embedded_empty_no_joint_parity, Bool.eq_false_iff.mpr ?_⟩
  intro h
  exact embedded_empty_not_entails
    ((existsEntails_iff_boundedCheckMixed B hB arrow [] embedded).mpr h)

/-- An explicit length-two signed hole, independent of a universal bound. -/
theorem extracted_bounded_hole :
    (extractS ExtractExamples.arrow ExtractExamples.antecedent ExtractExamples.consequent
      (false, false) (true, true)).BoundedHoleS 2 :=
  (SS2Self.boundedHoleS_iff _ _).mpr
    ⟨[], [0, 1], ExtractExamples.hole, by decide⟩

/-- The negative mixed example has a bounded extracted counterexample. -/
theorem extracted_bounded_false :
    boundedCheckMixed (fun _ _ _ _ => 2) ExtractExamples.arrow
      ExtractExamples.antecedent ExtractExamples.consequent = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rcases (boundedCheckMixed_eq_true _ _ _ _).mp h with hn | ⟨_, _, _, hh⟩
  · exact hn ExtractExamples.antecedent_sat
  · exact hh (false, false) (true, true) extracted_bounded_hole

/-- Kernel evaluation of the transported search, including a nonempty self guard. -/
theorem transported_search_positive :
    @decide (SS2SelfExamples.pending.BoundedHoleS 4)
      (SS2Self.decideBoundedHoleS SS2SelfExamples.pending 4) = true := by
  decide +kernel

/-- The unique underlying SS2 hole is removed by its strict target self event. -/
theorem transported_search_negative :
    @decide (SS2SelfExamples.uniqueBlocked.BoundedHoleS 1)
      (SS2Self.decideBoundedHoleS SS2SelfExamples.uniqueBlocked 1) = false := by
  decide +kernel

/-- A concrete extracted hole witnesses the short-bound hypotheses. -/
theorem short_hypotheses_nonvacuous :
    SS2SelfExamples.pending.FH ∧ SS2SelfExamples.pending.HasHoleS :=
  ⟨SS2SelfExamples.pending_hypotheses.1, SS2SelfExamples.pending_hypotheses.2.1⟩
end DecideMixedExamples

end Mixed
end DeciENSSE.Core
