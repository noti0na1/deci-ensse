import DeciENSSE.Core.Reduction
import DeciENSSE.Core.AutomataDecide

/-! # Existential entailment from a short-hole bound

A supplied short-hole bound turns the Horn characterization into a finite
exhaustive search over arbitrary finite visible and hidden variable types.

## Main declarations

- `SS2.BoundedHole`
- `boundedCheck`
- `existsEntails_iff_bounded`
- `decideExistsEntailsOfShortHoles`
-/

namespace DeciENSSE.Core
namespace SS2
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*}
  [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- Explicit finite enumeration of two words over the finite alphabet of total length at most L.
-/
def BoundedHole (I : SS2 α SA SB SC SD) (L : ℕ) : Prop :=
  ∃ n : Fin (L + 1), ∃ m : Fin (L + 1), n.val + m.val ≤ L ∧
    ∃ u : Fin n.val → α, ∃ t : Fin m.val → α,
      I.IsHole (List.ofFn u) (List.ofFn t)

instance instDecidableBoundedHole (I : SS2 α SA SB SC SD) (L : ℕ) :
    Decidable (I.BoundedHole L) := by
  unfold BoundedHole
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Finite-function enumeration is equivalent to bounded lists witnessing a hole. -/
theorem boundedHole_iff (I : SS2 α SA SB SC SD) (L : ℕ) :
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
def decideBoundedHoleFin (I : SS2 α SA SB SC SD) (L : ℕ) : Decidable (I.BoundedHole L) :=
  (Fintype.truncEquivFin SA).recOnSubsingleton fun a =>
  (Fintype.truncEquivFin SB).recOnSubsingleton fun b =>
  (Fintype.truncEquivFin SC).recOnSubsingleton fun c =>
  (Fintype.truncEquivFin SD).recOnSubsingleton fun d =>
    decidable_of_iff ((I.rename a b c d).BoundedHole L) (by
      rw [boundedHole_iff, boundedHole_iff, rename_boundedHole])

/-- The sole use of the universal bound is completeness of the finite search. -/
theorem hasHole_iff_bounded (I : SS2 α SA SB SC SD) (B : HoleBound)
    (hB : ShortHoleBound α B) (hfh : I.FH) :
    I.HasHole ↔ I.BoundedHole
      (B (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD)) := by
  rw [boundedHole_iff]
  exact ⟨shortHoleBound_transport I B hB hfh,
    fun ⟨u, t, hh, _⟩ => ⟨u, t, hh⟩⟩
end SS2

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Exact powerset state counts supplied to the external bound. -/
def extractedBound (B : HoleBound) (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  B (Fintype.card (Finset X)) (Fintype.card (Finset X))
    (Fintype.card (Finset (X ⊕ Z))) (Fintype.card (Finset (X ⊕ Z)))

/-- Logical specification of the finite procedure, meaningful for every B, including bounds for
which `ShortHoleBound (Fin n) B` has not been established. -/
def BoundedEntails (B : HoleBound) (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  (¬ ∃ ρ, Sat ρ φ) ∨ ((∃ ρ, Sat ρ ψ) ∧ CondI φ ψ ∧ CondII φ ψ ∧
    ∀ x y, ¬ (extract φ ψ x y).BoundedHole (extractedBound B X Z))

/-- Test satisfiability and the first two Horn conditions, then search for bounded holes. -/
def decideBoundedEntails (B : HoleBound) (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (BoundedEntails B φ ψ) := by
  letI := Bound.decideSat φ
  if hφ : ∃ ρ, Sat ρ φ then
    letI := Bound.decideSat ψ
    if hψ : ∃ ρ, Sat ρ ψ then
      letI := Bound.decideCondI φ ψ
      if hi : CondI φ ψ then
        letI := Bound.decideCondII φ ψ hφ hψ
        if hii : CondII φ ψ then
          letI (x y : X) := SS2.decideBoundedHoleFin (extract φ ψ x y) (extractedBound B X Z)
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
    {ψ : List (Lit n (X ⊕ Z))} (he : ExistsEntails φ ψ) : BoundedEntails B φ ψ := by
  classical
  by_cases hφ : ∃ ρ, Sat ρ φ
  · have hψ : ∃ ρ, Sat ρ ψ := by
      obtain ⟨ρ, hρ⟩ := hφ
      obtain ⟨σ, _, hσ⟩ := he ρ (fun _ => trivial) hρ
      exact ⟨_, hσ⟩
    obtain ⟨hi, hii, hh⟩ := (ss2_reduction hφ hψ).mp he
    refine Or.inr ⟨hψ, hi, hii, fun x y hb => ?_⟩
    obtain ⟨u, t, hu, _⟩ := (SS2.boundedHole_iff _ _).mp hb
    exact hh x y ⟨u, t, hu⟩
  · exact Or.inl hφ

/-- Bounded-search correctness: the bound supplies exactly the missing implication from absence of
short holes to absence of all holes. -/
theorem existsEntails_iff_bounded (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntails φ ψ ↔ BoundedEntails B φ ψ := by
  classical
  refine ⟨boundedEntails_of_entails B, ?_⟩
  rintro (hφ | ⟨hψ, hi, hii, hh⟩)
  · exact existsEntails_of_unsat hφ
  · by_cases hφ : ∃ ρ, Sat ρ φ
    · apply (ss2_reduction hφ hψ).mpr
      exact ⟨hi, hii, fun x y h => hh x y
        ((SS2.hasHole_iff_bounded _ B hB (extract_fh hi x y)).mp h)⟩
    · exact existsEntails_of_unsat hφ

/-- Entailment is equivalent to the explicit Boolean finite check under hB. -/
theorem existsEntails_iff_boundedCheck (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntails φ ψ ↔ boundedCheck B φ ψ = true :=
  (existsEntails_iff_bounded B hB φ ψ).trans (boundedCheck_eq_true B φ ψ).symm

/-- Bounded decision, for arbitrary finite visible and hidden variable types. -/
def decideExistsEntailsOfShortHoles (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Decidable (ExistsEntails φ ψ) := by
  letI := decideBoundedEntails B φ ψ
  exact decidable_of_iff (BoundedEntails B φ ψ) (existsEntails_iff_bounded B hB φ ψ).symm

/-- The bounded decision returns true exactly for existential entailment. -/
theorem decideExistsEntailsOfShortHoles_correct (B : HoleBound) (hB : ShortHoleBound (Fin n) B)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide (ExistsEntails φ ψ) (decideExistsEntailsOfShortHoles B hB φ ψ) = true ↔
      ExistsEntails φ ψ := by
  exact @decide_eq_true_iff _ (decideExistsEntailsOfShortHoles B hB φ ψ)

end DeciENSSE.Core
