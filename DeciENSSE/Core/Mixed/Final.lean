import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Core.Words.Self.BoundS
import DeciENSSE.Core.Nullary

/-! # Unconditional n-ary mixed existential entailment over arbitrary trees

The uniform self-aware hole bound gives a computable mixed entailment
decider over arbitrary trees, at every arity and variance. No parity or
short-hole premise remains in the final decision procedure.

## Main declarations

- `decideExistsEntailsAny`,
  `existsEntailsAny_iff_boundedCheck`, `decideExistsEntailsAny_correct`,
  `decideExistsEntailsAny_nullary_agrees`.
-/

set_option autoImplicit false

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A computable decision procedure for every arity and variance. -/
def decideExistsEntailsAny (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Decidable (ExistsEntailsT c φ ψ) :=
  decideExistsEntailsAnyOfShortHoles existsHoleBoundS (shortHoleBoundS (Fin n)) c φ ψ

/-- The unconditional bounded check is equivalent to existential entailment. -/
theorem existsEntailsAny_iff_boundedCheck (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ boundedCheckMixed existsHoleBoundS c φ ψ = true :=
  existsEntails_iff_boundedCheckMixed existsHoleBoundS (shortHoleBoundS (Fin n)) c φ ψ

/-- The unconditional decision returns true exactly for existential entailment. -/
theorem decideExistsEntailsAny_correct (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide (ExistsEntailsT c φ ψ) (decideExistsEntailsAny c φ ψ) = true ↔
      ExistsEntailsT c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAny c φ ψ)

/-- The general mixed endpoint agrees with the specialized nullary enumeration. -/
theorem decideExistsEntailsAny_nullary_agrees (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAny c φ ψ) =
      @decide _ (Nullary.decideExistsEntailsAny c φ ψ) :=
  (Nullary.decideExistsEntailsAny_agrees c φ ψ (decideExistsEntailsAny c φ ψ)).symm

namespace FinalMixedExamples
open LeafHornExamples ConditionsExamples

/-- The unconditional bounded check accepts an input without joint parity. -/
theorem mixed_positive :
    (¬ ∃ s : Bool ⊕ Unit → Bool,
      (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
      (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i))) ∧
    boundedCheckMixed existsHoleBoundS arrow mixed embedded = true :=
  DecideMixedExamples.mixed_positive existsHoleBoundS

/-- The unconditional bounded check rejects an input without joint parity. -/
theorem mixed_negative :
    (¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
    boundedCheckMixed existsHoleBoundS arrow [] embedded = false :=
  DecideMixedExamples.mixed_negative existsHoleBoundS (shortHoleBoundS (Fin 3))

/-- The final decision accepts the mixed example without joint parity. -/
theorem decision_positive :
    @decide (ExistsEntailsT arrow mixed embedded)
      (decideExistsEntailsAny arrow mixed embedded) = true :=
  (decideExistsEntailsAny_correct arrow mixed embedded).mpr embedded_entails

/-- The final decision rejects its empty-antecedent variant. -/
theorem decision_negative :
    @decide (ExistsEntailsT arrow [] embedded)
      (decideExistsEntailsAny arrow [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact embedded_empty_not_entails ((decideExistsEntailsAny_correct arrow [] embedded).mp h)

/-- The universal short-hole premise is proved, and has an actual FH hole. -/
theorem bound_nonvacuous : ShortHoleBoundS (Fin 3) existsHoleBoundS ∧
    NonMortalSExamples.ternaryPending.FH ∧ NonMortalSExamples.ternaryPending.HasHoleS :=
  ⟨shortHoleBoundS (Fin 3), NonMortalSExamples.ternaryPending_fh,
    [1, 2], [1, 2], NonMortalSExamples.ternary_pending_completion⟩

/-- A unary contravariant constructor system passes the final decision. -/
theorem unary_positive :
    @decide (ExistsEntailsT (fun _ : Fin 1 => true)
      [.lef () (fun _ => ())]
      ([.lef (.inl ()) (fun _ => .inl ())] : List (LitT 1 (Unit ⊕ Unit))))
      (decideExistsEntailsAny _ _ _) = true := by
  apply (decideExistsEntailsAny_correct _ _ _).mpr
  intro ρ _ hρ
  refine ⟨fun _ => DeciNSSE.Tree.bot, fun _ => trivial, ?_⟩
  simpa [SatT, HoldsT, Function.comp_def] using hρ

/-- Both outcomes of the nullary enumeration transfer to the general endpoint. -/
theorem nullary_positive :
    @decide (ExistsEntailsT Fin.elim0 [.bot 0, .top 1]
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit))))
      (decideExistsEntailsAny _ _ _) = true := by
  rw [decideExistsEntailsAny_nullary_agrees]
  decide +kernel

/-- The general decision rejects the displayed nullary non-entailment. -/
theorem nullary_negative :
    @decide (ExistsEntailsT Fin.elim0 [] ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit))))
      (decideExistsEntailsAny _ _ _) = false := by
  rw [decideExistsEntailsAny_nullary_agrees]
  decide +kernel

/-- A genuinely ternary bounded search, with a nonempty target self guard. -/
theorem ternary_search_positive :
    @decide (NonMortalSExamples.ternaryPending.BoundedHoleS 4)
      (SS2Self.decideBoundedHoleS NonMortalSExamples.ternaryPending 4) = true := by
  decide +kernel

/-- Empty alphabets still admit the pair of empty words and a nonempty self guard. -/
theorem nullary_search_positive :
    @decide (BoundSExamples.emptyInstance.BoundedHoleS 0)
      (SS2Self.decideBoundedHoleS BoundSExamples.emptyInstance 0) = true := by
  decide +kernel

end FinalMixedExamples

end DeciENSSE.Core.Mixed
