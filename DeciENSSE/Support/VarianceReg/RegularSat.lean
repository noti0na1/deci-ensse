import DeciNSSE.Satisfiability.ShapeGraph
import DeciNSSE.Satisfiability.FiniteVariance

/-! # Regular satisfiability

Signed translation and the regular fixed solution give a regular model whenever
an arbitrary model exists.

## Main declarations

- `satRegGen_iff_satGen`: regular and arbitrary satisfiability coincide.
-/

namespace DeciENSSE.Support
open DeciNSSE

/-- Regular satisfiability equals arbitrary satisfiability for every variance. -/
theorem satRegGen_iff_satGen {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) :
    (∃ σ : V k → RGraph n, Sat c (RGraph.unfold ∘ σ) ϕ) ↔ ∃ ρ, Sat c ρ ϕ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, hσ⟩
  · intro h
    have hs := (sat_iff_signed_sat c ϕ).mp h
    have hn : ¬ LabelClash (signed c ϕ) := fun hc => hc.unsatisfiable hs
    obtain ⟨hg, hfix⟩ := regular_fixed_solution c (SignSelection.signed_flipClosed c ϕ)
      (SignSelection.signed_signCoherent c ϕ) hn
    exact ⟨_, sat_decodedGraph c hg hfix⟩

end DeciENSSE.Support
