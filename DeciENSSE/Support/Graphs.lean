import DeciNSSE.Semantics.Regular
import DeciNSSE.Satisfiability.ShapeGraph
import DeciNSSE.Satisfiability.FiniteVariance

/-! # Graph unfoldings and regular satisfiability

An unfolding is a leaf or constructor according to the label at its root.

Signed translation and the regular fixed solution give a regular model whenever
an arbitrary model exists.

## Main declarations

- `RGraph.unfold_bot`
- `RGraph.unfold_top`
- `RGraph.unfold_node`
- `satReg_iff_sat`: regular and arbitrary satisfiability coincide.
-/

namespace DeciENSSE.Support.Graphs.RGraph
open DeciNSSE
variable {n : ℕ}
/-- A bottom root label unfolds to bottom. -/
theorem unfold_bot (g : RGraph n) (h : g.label g.root = Sym.bot) :
    g.unfold = DeciNSSE.Tree.bot := (DeciNSSE.Tree.root_eq_bot_iff _).mp (congrArg some h)

/-- A top root label unfolds to top. -/
theorem unfold_top (g : RGraph n) (h : g.label g.root = Sym.top) :
    g.unfold = DeciNSSE.Tree.top := (DeciNSSE.Tree.root_eq_top_iff _).mp (congrArg some h)
/-- A constructor root unfolds to the constructor of its child unfoldings. -/
theorem unfold_node (g : RGraph n) (h : g.label g.root = Sym.f) :
    g.unfold = DeciNSSE.Tree.node (fun i => (g.reroot (g.child g.root i)).unfold) := by
  apply DeciNSSE.Tree.ext
  funext w
  cases w with
  | nil => exact congrArg some h
  | cons i w =>
    change (g.walkFrom g.root (i :: w)).map g.label =
      ((g.reroot (g.child g.root i)).walkFrom (g.child g.root i) w).map g.label
    rw [RGraph.walkFrom, ite_eq_left h, RGraph.walkFrom_reroot]

end DeciENSSE.Support.Graphs.RGraph

namespace DeciENSSE.Support.Graphs
open DeciNSSE

/-- Regular satisfiability equals arbitrary satisfiability for every variance. -/
theorem satReg_iff_sat {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) :
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

end DeciENSSE.Support.Graphs
