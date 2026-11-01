import DeciENSSE.Core.Mixed.Extract
import DeciENSSE.Core.Mixed.CondI0
import DeciENSSE.Core.Mixed.Units

/-! # Conditional decision of n-ary mixed existential entailment

Combine satisfiability, unit conditions, and a finite self-aware hole search.
The only mathematical premise is a uniform short-hole bound.

## Main declarations

- `SelfTwoWordInstance.BoundedHole`, `SelfTwoWordInstance.decideBoundedHole`,
  `BoundedEntailsMixed`, `boundedCheckMixed`, `existsEntailsT_iff_boundedSelf`,
  `decideExistsEntailsOfShortHoles`.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self

namespace Words.Self.SelfTwoWordInstance
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- Finite enumeration of two words over a finite alphabet with total length at most L. -/
def BoundedHole (I : SelfTwoWordInstance α SA SB SC SD) (L : ℕ) : Prop :=
  ∃ n : Fin (L + 1), ∃ m : Fin (L + 1), n.val + m.val ≤ L ∧
    ∃ u : Fin n.val → α, ∃ t : Fin m.val → α,
      I.IsHole (List.ofFn u) (List.ofFn t)

/-- Finite word enumeration decides bounded hole existence. -/
instance instDecidableBoundedHole (I : SelfTwoWordInstance α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHole L) := by
  unfold BoundedHole
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Finite tuple enumeration is equivalent to a total word-length bound. -/
theorem boundedHole_iff (I : SelfTwoWordInstance α SA SB SC SD) (L : ℕ) :
    I.BoundedHole L ↔ ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ L := by
  constructor
  · rintro ⟨n, m, hlen, u, t, hh⟩
    exact ⟨List.ofFn u, List.ofFn t, hh, by simpa using hlen⟩
  · rintro ⟨u, t, hh, hlen⟩
    refine ⟨⟨u.length, by omega⟩, ⟨t.length, by omega⟩, hlen,
      (fun i => u[i]), (fun i => t[i]), ?_⟩
    simpa using hh

/-- Computable Fin transport, including both coordinates of the self guard. Truncated equivalences
eliminate into the subsingleton `Decidable P`. -/
def decideBoundedHole (I : SelfTwoWordInstance α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHole L) :=
  (Fintype.truncEquivFin SA).recOnSubsingleton fun a =>
  (Fintype.truncEquivFin SB).recOnSubsingleton fun b =>
  (Fintype.truncEquivFin SC).recOnSubsingleton fun c =>
  (Fintype.truncEquivFin SD).recOnSubsingleton fun d =>
    decidable_of_iff ((I.rename a b c d).BoundedHole L) (by
      rw [boundedHole_iff, boundedHole_iff, rename_boundedHole])

/-- The universal bound is used only to complete the bounded hole search. -/
theorem hasHole_iff_bounded (I : SelfTwoWordInstance α SA SB SC SD) (B : HoleBound)
    (hB : ShortHoleBoundSelf α B) (hfh : I.ForcedHeads) :
    I.HasHole ↔ I.BoundedHole
      (B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD)) := by
  rw [boundedHole_iff]
  exact ⟨shortHoleBoundSelf_transport I B hB hfh,
    fun ⟨u, t, hh, _⟩ => ⟨u, t, hh⟩⟩
end Words.Self.SelfTwoWordInstance

namespace Mixed
open DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Exact extraction sizes, including the sticky flag and consequent upper summary in the target
state. -/
def extractedBoundSelf (B : HoleBound) (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  B (Fintype.card (Finset (X × Bool))) (Fintype.card (TargetState X Z))
    (Fintype.card (Finset ((X ⊕ Z) × Bool)))
    (Fintype.card (Finset ((X ⊕ Z) × Bool)))

/-- Specification of the finite procedure. Satisfiability, I0 and U use their finite deciders; the
remaining quantifiers enumerate signed visible variables and pairs of bounded words over Fin
n. -/
def BoundedEntailsMixed (B : HoleBound) (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  (¬ ∃ ρ, SatT c ρ φ) ∨ ((∃ ρ, SatT c ρ ψ) ∧ CondI0 c φ ψ ∧ CondU c φ ψ ∧
    ∀ p q, ¬ (extractSelf c φ ψ p q).BoundedHole (extractedBoundSelf B X Z))

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
          letI (p q : X × Bool) := SelfTwoWordInstance.decideBoundedHole (extractSelf c φ ψ p q)
            (extractedBoundSelf B X Z)
          exact decidable_of_iff
            (∀ p q, ¬ (extractSelf c φ ψ p q).BoundedHole (extractedBoundSelf B X Z))
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
    obtain ⟨u, t, ht, _⟩ := (SelfTwoWordInstance.boundedHole_iff _ _).mp hb
    exact hh p q ⟨u, t, ht⟩
  · exact Or.inl hφ

/-- Correctness using the forced target heads theorem of extraction. -/
theorem existsEntailsT_iff_boundedSelf (B : HoleBound) (hB : ShortHoleBoundSelf (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ BoundedEntailsMixed B c φ ψ := by
  classical
  refine ⟨boundedEntailsMixed_of_entails B, ?_⟩
  rintro (hφ | ⟨hψ, hi, hu, hh⟩)
  · exact existsEntailsT_of_unsat hφ
  · by_cases hφ : ∃ ρ, SatT c ρ φ
    · apply (mixed_reduction hφ hψ).mpr
      exact ⟨hi, hu, fun p q h => hh p q
        ((SelfTwoWordInstance.hasHole_iff_bounded _ B hB (extractSelf_forcedHeads p q)).mp h)⟩
    · exact existsEntailsT_of_unsat hφ

/-- A uniform short-hole bound makes the Boolean check exact. -/
theorem existsEntails_iff_boundedCheckMixed (B : HoleBound) (hB : ShortHoleBoundSelf (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔ boundedCheckMixed B c φ ψ = true :=
  (existsEntailsT_iff_boundedSelf B hB c φ ψ).trans
    (boundedCheckMixed_eq_true B c φ ψ).symm

/-- Arbitrary-tree existential entailment, for every variance and finite visible/hidden carriers.
The bound proof is the only mathematical premise. -/
def decideExistsEntailsOfShortHoles (B : HoleBound) (hB : ShortHoleBoundSelf (Fin n) B)
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsT c φ ψ) := by
  letI := decideBoundedEntailsMixed B c φ ψ
  exact decidable_of_iff (BoundedEntailsMixed B c φ ψ)
    (existsEntailsT_iff_boundedSelf B hB c φ ψ).symm

end Mixed
end DeciENSSE.Core
