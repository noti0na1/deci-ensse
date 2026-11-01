import DeciNSSE.Semantics.Regular

/-! # Root equations for graph unfoldings

An unfolding is a leaf or constructor according to the label at its root.

## Main declarations

- `RGraphN.unfold_bot`
- `RGraphN.unfold_top`
- `RGraphN.unfold_node`
-/

namespace DeciENSSE.Support.RGraphN
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

end DeciENSSE.Support.RGraphN
