import DeciENSSE.Support.Transfer.RankedExtension
import DeciNSSE.Satisfiability.Finite


/-! # Finite satisfiability of ranked extensions

Cycle clashes are preserved and reflected by ranked extensions. A satisfiable
extension has a finite solution whenever its original system does.

## Main declarations

- `FinT.extension_cycleClash_iff`
- `FinT.extension_satFin_iff`
-/

namespace DeciENSSE.Support.FinT
open DeciNSSE


variable {n k m : ℕ}

section Extension

variable {ϕ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

/-- The old block of a solution of an extension solves the base system. -/
theorem extension_restrict_sat (e : Ranked.ExtensionN ϕ ψ Source Sink rank)
    {ρ' : V (k + m) → DeciNSSE.Tree n} (h : Covariant.Sat ρ' ψ) : Covariant.Sat (ρ' ∘ Fin.castAdd m)
      ϕ := by
  intro l hl
  exact (Lit.holds_rename _ _ _).mp (h _ (e.old_mem l hl))

/-- A ranked extension has a cycle clash exactly when its base has one. -/
theorem extension_cycleClash_iff (e : Ranked.ExtensionN ϕ ψ Source Sink rank) :
    DeciNSSE.CycleClash ψ ↔ DeciNSSE.CycleClash ϕ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.old_mem, hd.map _ e.old_mem, hu.map _ e.old_mem⟩

/-- A ranked extension is finitely satisfiable exactly when it is satisfiable and
its base is finitely satisfiable. -/
theorem extension_satFin_iff (e : Ranked.ExtensionN ϕ ψ Source Sink rank) :
    (∃ σ : V (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨_, hσ⟩, ⟨σ ∘ Fin.castAdd m, extension_restrict_sat e hσ⟩⟩
  · rintro ⟨⟨ρ', hρ'⟩, hf⟩
    apply DeciNSSE.satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ', hρ'⟩,
      fun hc => (DeciNSSE.satFin_iff.mp hf).2 ((extension_cycleClash_iff e).mp hc)⟩

end Extension


end DeciENSSE.Support.FinT
