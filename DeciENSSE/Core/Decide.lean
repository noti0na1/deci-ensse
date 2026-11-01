import DeciENSSE.Core.Reduction
import DeciENSSE.Core.AutomataDecide

/-! # Bounded search for covariant existential entailment

A short-hole bound makes the two-word reduction executable: first test
satisfiability, then (I0) and liveness, then enumerate the bounded spine and
target words for each visible variable pair. `existsEntails_iff_bounded`
proves that this finite search is equivalent to existential entailment.

This is the decision step of the covariant proof, parameterized by a bound.
`Core/Final` supplies the bound proved in the word layer. Renaming automaton
states to finite index types keeps the search computable for any finite
state carriers.

## Main declarations

- `Words.TwoWordInstance.BoundedHole`: the finite two-word search space.
- `BoundedEntails`, `boundedCheck`: the logical and Boolean bounded tests.
- `existsEntails_iff_bounded`: correctness under a short-hole bound.
- `decideExistsEntailsTopFreeOfShortHoles`: the resulting entailment decider.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Words.TwoWordInstance
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- Explicit finite enumeration of two words over the finite alphabet of total length at most L.
-/
def BoundedHole (I : TwoWordInstance α SA SB SC SD) (L : ℕ) : Prop :=
  ∃ n : Fin (L + 1), ∃ m : Fin (L + 1), n.val + m.val ≤ L ∧
    ∃ u : Fin n.val → α, ∃ t : Fin m.val → α,
      I.IsHole (List.ofFn u) (List.ofFn t)

instance instDecidableBoundedHole (I : TwoWordInstance α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHole L) := by
  unfold BoundedHole
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Finite-function enumeration is equivalent to bounded lists witnessing a hole. -/
theorem boundedHole_iff (I : TwoWordInstance α SA SB SC SD) (L : ℕ) :
    I.BoundedHole L ↔ ∃ u t, I.IsHole u t ∧ u.length + t.length ≤ L := by
  constructor
  · rintro ⟨n, m, hlen, u, t, hh⟩
    exact ⟨List.ofFn u, List.ofFn t, hh, by simpa using hlen⟩
  · rintro ⟨u, t, hh, hlen⟩
    refine ⟨⟨u.length, by omega⟩, ⟨t.length, by omega⟩, hlen,
      (fun i => u[i]), (fun i => t[i]), ?_⟩
    simpa using hh

/-- Search the renamed Fin instance. Truncated equivalences can be eliminated computably because
`Decidable P` is a subsingleton. No chosen enumeration or classical decision oracle enters the
executable code. -/
def decideBoundedHoleFin (I : TwoWordInstance α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHole L) :=
  (Fintype.truncEquivFin SA).recOnSubsingleton fun a =>
  (Fintype.truncEquivFin SB).recOnSubsingleton fun b =>
  (Fintype.truncEquivFin SC).recOnSubsingleton fun c =>
  (Fintype.truncEquivFin SD).recOnSubsingleton fun d =>
    decidable_of_iff ((I.rename a b c d).BoundedHole L) (by
      rw [boundedHole_iff, boundedHole_iff, rename_boundedHole])

/-- The sole use of the universal bound is completeness of the finite search. -/
theorem hasHole_iff_bounded (I : TwoWordInstance α SA SB SC SD) (B : HoleBound)
    (hB : ShortHoleBound α B) (hfh : I.ForcedHeads) :
    I.HasHole ↔ I.BoundedHole
      (B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD)) := by
  rw [boundedHole_iff]
  exact ⟨shortHoleBound_transport I B hB hfh,
    fun ⟨u, t, hh, _⟩ => ⟨u, t, hh⟩⟩
end Words.TwoWordInstance

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Exact powerset state counts supplied to the short-hole bound. -/
def extractedBound (B : HoleBound) (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  B (Fintype.card (Finset X)) (Fintype.card (Finset X))
    (Fintype.card (Finset (X ⊕ Z))) (Fintype.card (Finset (X ⊕ Z)))

/-- Logical specification of the finite procedure, meaningful for every B, including bounds for
which `ShortHoleBound (Fin n) B` has not been established. -/
def BoundedEntails (B : HoleBound) (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  (¬ ∃ ρ, Sat ρ φ) ∨ ((∃ ρ, Sat ρ ψ) ∧ CondI0 φ ψ ∧ CondLive φ ψ ∧
    ∀ x y, ¬ (extract φ ψ x y).BoundedHole (extractedBound B X Z))

/-- Test satisfiability, (I0), and liveness, then search for bounded holes. -/
def decideBoundedEntails (B : HoleBound) (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (BoundedEntails B φ ψ) := by
  letI := Automata.decideSat φ
  if hφ : ∃ ρ, Sat ρ φ then
    letI := Automata.decideSat ψ
    if hψ : ∃ ρ, Sat ρ ψ then
      letI := Automata.decideCondI0 φ ψ
      if hi : CondI0 φ ψ then
        letI := Automata.decideCondLive φ ψ hφ hψ
        if hii : CondLive φ ψ then
          letI (x y : X) := TwoWordInstance.decideBoundedHoleFin
            (extract φ ψ x y) (extractedBound B X Z)
          exact decidable_of_iff
            (∀ x y, ¬ (extract φ ψ x y).BoundedHole (extractedBound B X Z))
            (by simp [BoundedEntails, hφ, hψ, hi, hii])
        else
          exact isFalse (by simp [BoundedEntails, hφ, hii])
      else
        exact isFalse (by simp [BoundedEntails, hφ, hi])
    else
      exact isFalse (by simp [BoundedEntails, hφ, hψ])
  else
    exact isTrue (Or.inl hφ)

/-- The executable Boolean finite check. -/
def boundedCheck (B : HoleBound) (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Bool :=
  @decide (BoundedEntails B φ ψ) (decideBoundedEntails B φ ψ)

/-- The Boolean bounded check recognizes the bounded entailment condition. -/
theorem boundedCheck_eq_true (B : HoleBound) (φ : List (Lit n X))
    (ψ : List (Lit n (X ⊕ Z))) : boundedCheck B φ ψ = true ↔ BoundedEntails B φ ψ := by
  exact @decide_eq_true_iff _ (decideBoundedEntails B φ ψ)

/-- A negative finite result is sound even without a universal bound. -/
theorem boundedEntails_of_entails (B : HoleBound) {φ : List (Lit n X)}
    {ψ : List (Lit n (X ⊕ Z))} (he : ExistsEntailsTopFree φ ψ) : BoundedEntails B φ ψ := by
  classical
  by_cases hφ : ∃ ρ, Sat ρ φ
  · have hψ : ∃ ρ, Sat ρ ψ := by
      obtain ⟨ρ, hρ⟩ := hφ
      obtain ⟨σ, _, hσ⟩ := he ρ (fun _ => trivial) hρ
      exact ⟨_, hσ⟩
    obtain ⟨hi, hii, hh⟩ := (ss2_reduction hφ hψ).mp he
    refine Or.inr ⟨hψ, hi, hii, fun x y hb => ?_⟩
    obtain ⟨u, t, hu, _⟩ := (TwoWordInstance.boundedHole_iff _ _).mp hb
    exact hh x y ⟨u, t, hu⟩
  · exact Or.inl hφ

/-- Bounded-search correctness: the bound supplies exactly the missing implication from absence of
short holes to absence of all holes. -/
theorem existsEntails_iff_bounded (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsTopFree φ ψ ↔ BoundedEntails B φ ψ := by
  classical
  refine ⟨boundedEntails_of_entails B, ?_⟩
  rintro (hφ | ⟨hψ, hi, hii, hh⟩)
  · exact existsEntails_of_unsat hφ
  · by_cases hφ : ∃ ρ, Sat ρ φ
    · apply (ss2_reduction hφ hψ).mpr
      exact ⟨hi, hii, fun x y h => hh x y
        ((TwoWordInstance.hasHole_iff_bounded _ B hB (extract_forcedHeads hi x y)).mp h)⟩
    · exact existsEntails_of_unsat hφ

/-- Entailment is equivalent to the explicit Boolean finite check under hB. -/
theorem existsEntails_iff_boundedCheck (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsTopFree φ ψ ↔ boundedCheck B φ ψ = true :=
  (existsEntails_iff_bounded B hB φ ψ).trans (boundedCheck_eq_true B φ ψ).symm

/-- Bounded decision, for arbitrary finite visible and hidden variable types. -/
def decideExistsEntailsTopFreeOfShortHoles (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Decidable (ExistsEntailsTopFree φ ψ) := by
  letI := decideBoundedEntails B φ ψ
  exact decidable_of_iff (BoundedEntails B φ ψ) (existsEntails_iff_bounded B hB φ ψ).symm

/-- The bounded decision returns true exactly for existential entailment. -/
theorem decideExistsEntailsTopFreeOfShortHoles_correct (B : HoleBound)
    (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide (ExistsEntailsTopFree φ ψ) (decideExistsEntailsTopFreeOfShortHoles B hB φ ψ) = true ↔
      ExistsEntailsTopFree φ ψ := by
  exact @decide_eq_true_iff _ (decideExistsEntailsTopFreeOfShortHoles B hB φ ψ)

end DeciENSSE.Core
