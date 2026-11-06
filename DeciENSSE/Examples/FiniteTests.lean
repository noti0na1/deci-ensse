import DeciENSSE.Examples.Public

/-! # Both finite-satisfiability tests are needed

This module proves the two systems in `rem:tc-examples` of the paper for every
positive arity and every variance. `cycle_classes` uses no visible variables:
the empty antecedent entails a hidden constructor fixed point over arbitrary and
regular trees, but not finite trees. `cycleBottom_classes` reverses the outcome:
a visible fixed point does not entail bottom over arbitrary or regular trees,
but does so vacuously over finite trees. `cycle_unique` identifies the unique
(tree, not graph presentation) witness as `RGraph.allF n |>.unfold`.

`cycle_sat_iff` and `cycle_finite_unsatisfiable` give the satisfiability facts
behind both examples. `finite_leaf_intersection_not_finite` proves the remark's
last assertion about intersection, using the finite operands bottom and top.
The top-free variants give the same examples over `{⊥, f}`,
whose public semantics fixes the variance to covariance. The unary examples of
`Public` are the case `n = 1`; `cycle_at` also allows their unused visible variable.
-/

namespace DeciENSSE.Examples
open DeciNSSE

/-- A constructor fixed point at any variable, generalizing `unaryCycle`. -/
def cycle_at {n k : ℕ} (v : V k) : EConstraint n k :=
  [.leF v (fun _ => v), .fLe (fun _ => v) v]

/-- The same two literals in the bottom–constructor syntax. -/
def cycleTopFree_at {n k : ℕ} (v : V k) : BFConstraint n k :=
  [.leF v (fun _ => v), .fLe (fun _ => v) v]

/-- A constructor fixed point is uniquely the all-constructor tree, at any arity. -/
theorem cycle_unique {n : ℕ} (c : Fin n → Bool) (t : Tree n) :
    (Tree.Le c t (DeciNSSE.Tree.node fun _ => t) ∧ Tree.Le c (DeciNSSE.Tree.node fun _ => t) t) ↔
      t = (RGraph.allF n).unfold := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have he := treeLe_antisymm hlo hhi
    apply Tree.ext
    funext w
    rw [RGraph.allF_unfold_fn]
    induction w with
    | nil => exact congrArg (fun u : Tree n => u.fn []) he
    | cons i w ih =>
      calc
        t.fn (i :: w) = t.fn w := congrArg (fun u : Tree n => u.fn (i :: w)) he
        _ = some Sym.f := ih
  · rintro rfl
    rw [← RGraph.allF_unfold_node]
    exact ⟨treeLe_refl _ _, treeLe_refl _ _⟩

/-- Satisfaction of either cycle is exactly the unique-witness equation. -/
theorem cycle_sat_iff {n k : ℕ} (c : Fin n → Bool) (ρ : V k → Tree n) (v : V k) :
    ESat c ρ (cycle_at v) ↔ ρ v = (RGraph.allF n).unfold := by
  simpa [ESat, cycle_at, ELit.holds, Function.comp_def] using cycle_unique c (ρ v)

/-- Positive arity excludes every finite solution, independently of variance. -/
theorem cycle_finite_unsatisfiable {n k : ℕ} (hn : 1 ≤ n) (c : Fin n → Bool)
    (ρ : V k → FTree n) (v : V k) : ¬ ESat c (FTree.toTree ∘ ρ) (cycle_at v) := by
  intro h
  exact Core.Mixed.allF_not_finite ⟨0, hn⟩
    ⟨ρ v, (cycle_sat_iff c _ v).mp h⟩

/-- First system of `rem:tc-examples`, with exactly `X = ∅` and one hidden variable. -/
theorem cycle_classes {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Bool) :
    ExistsEntails (k := 0) (h := 1) c [] (cycle_at 0) ∧
    ExistsEntailsReg (k := 0) (h := 1) c [] (cycle_at 0) ∧
    ¬ ExistsEntailsFin (k := 0) (h := 1) c [] (cycle_at 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ _
    refine ⟨fun _ => (RGraph.allF n).unfold, (cycle_sat_iff _ _ _).mpr ?_⟩
    rfl
  · intro ρ _
    refine ⟨fun _ => RGraph.allF n, (cycle_sat_iff _ _ _).mpr ?_⟩
    rfl
  · intro H
    obtain ⟨σ, hs⟩ := H Fin.elim0 (by simp [ESat])
    exact Core.Mixed.allF_not_finite ⟨0, hn⟩
      ⟨σ 0, (cycle_sat_iff c _ 0).mp hs⟩

/-- Second system of `rem:tc-examples`, with one visible and no hidden variables. -/
theorem cycleBottom_classes {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Bool) :
    ¬ ExistsEntails (k := 1) (h := 0) c (cycle_at 0) [.eqBot (Fin.castAdd 0 0)] ∧
    ¬ ExistsEntailsReg (k := 1) (h := 0) c (cycle_at 0) [.eqBot (Fin.castAdd 0 0)] ∧
    ExistsEntailsFin (k := 1) (h := 0) c (cycle_at 0) [.eqBot (Fin.castAdd 0 0)] := by
  have hne : (RGraph.allF n).unfold ≠ Tree.bot := by
    rw [RGraph.allF_unfold_node]
    exact DeciNSSE.Tree.node_ne_bot _
  refine ⟨?_, ?_, ?_⟩
  · intro H
    obtain ⟨σ, hs⟩ := H (fun _ => (RGraph.allF n).unfold)
      ((cycle_sat_iff _ _ _).mpr rfl)
    exact hne (hs _ (List.mem_singleton_self _))
  · intro H
    obtain ⟨σ, hs⟩ := H (fun _ => RGraph.allF n) ((cycle_sat_iff _ _ _).mpr rfl)
    exact hne (hs _ (List.mem_singleton_self _))
  · intro ρ hs
    exact (cycle_finite_unsatisfiable hn c ρ 0 hs).elim

/-- First system over `{⊥, f}`, in all three tree classes. -/
theorem cycle_classes_topFree {n : ℕ} (hn : 1 ≤ n) :
    ExistsEntailsTopFree (k := 0) (h := 1) [] (cycleTopFree_at (n := n) 0) ∧
    ExistsEntailsTopFreeReg (k := 0) (h := 1) [] (cycleTopFree_at (n := n) 0) ∧
    ¬ ExistsEntailsTopFreeFin (k := 0) (h := 1) [] (cycleTopFree_at (n := n) 0) := by
  have htf : TopFree (RGraph.allF n).unfold := by
    intro w
    rw [RGraph.allF_unfold_fn]
    decide
  refine ⟨?_, ?_, ?_⟩
  · intro ρ _ _
    exact ⟨fun _ => (RGraph.allF n).unfold, fun _ => htf,
      (cycle_sat_iff _ _ _).mpr rfl⟩
  · intro ρ _ _
    exact ⟨fun _ => RGraph.allF n, fun _ => htf, (cycle_sat_iff _ _ _).mpr rfl⟩
  · intro H
    obtain ⟨σ, _, hs⟩ := H Fin.elim0 (fun v => Fin.elim0 v) (by simp [BFSat, ESat])
    exact Core.Mixed.allF_not_finite ⟨0, hn⟩
      ⟨σ 0, (cycle_sat_iff (fun _ => false) _ 0).mp hs⟩

/-- Second system over `{⊥, f}`; finite entailment again holds by inconsistency. -/
theorem cycleBottom_classes_topFree {n : ℕ} (hn : 1 ≤ n) :
    ¬ ExistsEntailsTopFree (k := 1) (h := 0) (cycleTopFree_at (n := n) 0)
      [.eqBot (Fin.castAdd 0 0)] ∧
    ¬ ExistsEntailsTopFreeReg (k := 1) (h := 0) (cycleTopFree_at (n := n) 0)
      [.eqBot (Fin.castAdd 0 0)] ∧
    ExistsEntailsTopFreeFin (k := 1) (h := 0) (cycleTopFree_at (n := n) 0)
      [.eqBot (Fin.castAdd 0 0)] := by
  have htf : TopFree (RGraph.allF n).unfold := by
    intro w
    rw [RGraph.allF_unfold_fn]
    decide
  have hne : (RGraph.allF n).unfold ≠ Tree.bot := by
    rw [RGraph.allF_unfold_node]
    exact DeciNSSE.Tree.node_ne_bot _
  refine ⟨?_, ?_, ?_⟩
  · intro H
    obtain ⟨σ, _, hs⟩ := H (fun _ => (RGraph.allF n).unfold) (fun _ => htf)
      ((cycle_sat_iff _ _ _).mpr rfl)
    exact hne (hs _ (List.mem_singleton_self _))
  · intro H
    obtain ⟨σ, _, hs⟩ := H (fun _ => RGraph.allF n) (fun _ => htf)
      ((cycle_sat_iff _ _ _).mpr rfl)
    exact hne (hs _ (List.mem_singleton_self _))
  · intro ρ _ hs
    exact (cycle_finite_unsatisfiable hn (fun _ => false) ρ 0 hs).elim

/-- Finite trees are not closed under intersection of signed leaf cones (`rem:tc-examples`). -/
theorem finite_leaf_intersection_not_finite {n : ℕ} (hn : 1 ≤ n) (c : Fin n → Bool) :
    ¬ ∃ a : FTree n, a.toTree = Core.Mixed.infoInter c Tree.bot Tree.top := by
  rw [Core.Mixed.infoInter_bot_top]
  exact Core.Mixed.allF_not_finite ⟨0, hn⟩

end DeciENSSE.Examples
