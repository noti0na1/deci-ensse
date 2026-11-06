import DeciENSSE.Core.Mixed.Extract

/-! # Countermodels from extracted holes

This module proves part (2) of `thm:ex-reduction`.
`extractSelf_hole_not_projected` excludes a Horn model extending the singleton
closure, and `extractSelf_hole_countermodel` decodes that closure to a solution
with no hidden extension. The hypotheses are exactly those of the reduction:
the antecedent is satisfiable and condition (U) holds.

The paths are named as in the paper: in `IsHole u t`, `t` is the seed path and
`u` is the output path, so the seed is `(p.1, p.2, t)`.

## Main declarations

- `extractSelf_hole_not_projected`: no model of the consequent extends the closure.
- `extractSelf_hole_countermodel`: the decoded countermodel.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*}
  [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
  {p q : X × Bool} {u t : List (Fin n)}

/-- `thm:ex-reduction`(2), at the level of Horn models. -/
theorem extractSelf_hole_not_projected (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    (hh : (extractSelf c φ ψ p q).IsHole u t) :
    ¬ ∃ T, Sol c ψ T ∧ restrict T = Cl c φ (p.1, p.2, t) := by
  obtain ⟨_, hm, hn⟩ := (extractSelf_isHoleS_iff p q hφ hU u t).mp hh
  rintro ⟨T, hT, he⟩
  have ha : visible (p.1, p.2, t) ∈ T := by
    change (p.1, p.2, t) ∈ restrict T
    rw [he]
    exact mem_cl.mpr (Or.inr .refl)
  have hb := (moves_reach hm).mem_of_closed hT.closed ha
  apply hn
  rw [← he]
  exact hb

/-- `thm:ex-reduction`(2): the solution decoded from the least model
is a countermodel, with its exact atom set recorded. -/
theorem extractSelf_hole_countermodel (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    (hh : (extractSelf c φ ψ p q).IsHole u t) :
    Sol c φ (Cl c φ (p.1, p.2, t)) ∧
      ∃ ρ, SatT c ρ φ ∧ configSet c ρ = Cl c φ (p.1, p.2, t) ∧
        ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  have hs := sol_cl ((extractSelf_isHoleS_iff p q hφ hU u t).mp hh).1
  obtain ⟨ρ, hρ, he⟩ := sol_iff_assignment.mp hs
  refine ⟨hs, ρ, hρ, he, ?_⟩
  rw [← projected_configSet, he]
  exact extractSelf_hole_not_projected hφ hU hh

end DeciENSSE.Core.Mixed
