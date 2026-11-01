import DeciENSSE.Core.Full.Flatten
import DeciENSSE.Support.Graphs
import DeciENSSE.Support.Nullary
import DeciENSSE.Core.Full.Classes
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Graph equations pin regular trees

Finite graph equations characterize each unfolding uniquely. Adding these
equations preserves visible regular values when choosing a regular solution.

## Main declarations

- `TopGraphs.Model`
- `TopGraphs.model_unique`
- `TopGraphs.equations`
- `TopGraphs.regularize`: preserve graph bounds at any variance and arity.
-/

namespace DeciENSSE.Core.Full.TopGraphs
open DeciNSSE

variable {n : ℕ} {I V : Type*}
/-- The disjoint union of the graph state sets. -/
abbrev States (g : I → RGraph n) := Σ i, Fin (g i).size

/-- The tree expression prescribed by a graph state. -/
def rhs (g : I → RGraph n) (τ : States g → DeciNSSE.Tree n) (i : I) (q : Fin (g i).size) :=
  match (g i).label q with
  | .bot => DeciNSSE.Tree.bot
  | .top => DeciNSSE.Tree.top
  | .f => DeciNSSE.Tree.node (fun j => τ ⟨i, (g i).child q j⟩)

/-- An assignment satisfying the equation at every graph state. -/
def Model (g : I → RGraph n) (τ : States g → DeciNSSE.Tree n) : Prop :=
  ∀ i q, τ ⟨i,q⟩ = rhs g τ i q

/-- Unfold each graph from the designated state. -/
def values (g : I → RGraph n) (q : States g) : DeciNSSE.Tree n := ((g q.1).reroot q.2).unfold

/-- Graph unfoldings satisfy their state equations. -/
theorem values_model (g : I → RGraph n) : Model g (values g) := by
  intro i q
  cases hl : (g i).label q with
  | bot => simpa only [rhs, hl, values] using Support.Graphs.RGraph.unfold_bot ((g i).reroot q) hl
  | top => simpa only [rhs, hl, values] using Support.Graphs.RGraph.unfold_top ((g i).reroot q) hl
  | f =>
    change ((g i).reroot q).unfold = _
    rw [Support.Graphs.RGraph.unfold_node _ hl]
    simp only [rhs, hl]
    congr 1

/-- Every solution of the graph equations equals the unfolding assignment. -/
theorem model_unique (g : I → RGraph n) {τ : States g → DeciNSSE.Tree n}
    (h : Model g τ) : τ = values g := by
  have hw : ∀ w : List (Fin n), ∀ i q,
      (τ ⟨i,q⟩).fn w = (values g ⟨i,q⟩).fn w := by
    intro w
    induction w with
    | nil =>
      intro i q
      rw [h i q, values_model g i q]
      cases hl : (g i).label q <;> simp [rhs, hl]
    | cons j w ih =>
      intro i q
      rw [h i q, values_model g i q]
      cases hl : (g i).label q with
      | bot => simp [rhs, hl]
      | top => simp [rhs, hl]
      | f =>
        simpa only [rhs, hl, DeciNSSE.Tree.node_fn_cons] using ih i ((g i).child q j)
  funext q
  exact DeciNSSE.Tree.ext (funext fun w => hw w q.1 q.2)

/-- Flat literals expressing the equation at one graph state. -/
def equationsAt (g : I → RGraph n) (q : States g) : List (LitT n (States g)) :=
  match (g q.1).label q.2 with
  | .bot => [.bot q]
  | .top => [.top q]
  | .f => [.fle (fun j => ⟨q.1, (g q.1).child q.2 j⟩) q,
      .lef q (fun j => ⟨q.1, (g q.1).child q.2 j⟩)]

/-- Collect the equations at every state of every graph. -/
noncomputable def equations [Fintype I] (g : I → RGraph n) : List (LitT n (States g)) :=
  Finset.univ.toList.flatMap (equationsAt g)

/-- Satisfying the graph literals is equivalent to solving its state equations. -/
theorem sat_equations [Fintype I] (c : Fin n → Bool) (g : I → RGraph n)
    (τ : States g → DeciNSSE.Tree n) :
    SatT c τ (equations g) ↔ Model g τ := by
  simp only [equations, SatT, List.forall_mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, forall_const]
  constructor
  · intro h i q
    have hh := h ⟨i,q⟩
    cases hl : (g i).label q <;>
      simp only [equationsAt, hl, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, HoldsT, rhs] at hh ⊢
    · exact hh
    · exact DeciNSSE.treeLe_antisymm hh.2 hh.1
    · exact hh
  · intro h ⟨i,q⟩
    have hh := h i q
    cases hl : (g i).label q <;>
      simp only [equationsAt, hl, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, HoldsT, rhs] at hh ⊢
    · exact hh
    · rw [hh]; exact ⟨DeciNSSE.treeLe_refl _ _, DeciNSSE.treeLe_refl _ _⟩
    · exact hh

/-- A bound between an old variable and a designated graph root. -/
abbrev Binding (V I : Type*) := V × I × Bool

/-- Interpret a comparison between a variable and a designated graph root. -/
def bindingHolds (c : Fin n → Bool) (g : I → RGraph n) (ρ : V → DeciNSSE.Tree n)
    (b : Binding V I) : Prop :=
  if b.2.2 then DeciNSSE.Tree.Le c (g b.2.1).unfold (ρ b.1)
  else DeciNSSE.Tree.Le c (ρ b.1) (g b.2.1).unfold

/-- Encode a comparison with a graph root as a flat literal. -/
def bindingLit (g : I → RGraph n) (b : Binding V I) : LitT n (V ⊕ States g) :=
  if b.2.2 then .le (.inr ⟨b.2.1, (g b.2.1).root⟩) (.inl b.1)
  else .le (.inl b.1) (.inr ⟨b.2.1, (g b.2.1).root⟩)

private theorem root_value (g : I → RGraph n) (i : I) :
    values g ⟨i,(g i).root⟩ = (g i).unfold := rfl

private theorem binding_spec (c : Fin n → Bool) (g : I → RGraph n)
    (τ : V ⊕ States g → DeciNSSE.Tree n)
    (h : τ ∘ Sum.inr = values g) (b : Binding V I) :
    HoldsT c τ (bindingLit g b) ↔ bindingHolds c g (τ ∘ Sum.inl) b := by
  have he := congrFun h ⟨b.2.1, (g b.2.1).root⟩
  simp only [Function.comp_apply, root_value] at he
  cases hb : b.2.2 <;> simp [bindingLit, bindingHolds, hb, HoldsT, he]

/-- Finitely many inequalities to regular graph values can be preserved while
regularizing a satisfiable full-signature assignment. The arity split supplies
`NeZero n` for constructor sandwiches; nullary trees already have presentations. -/
theorem regularize [Fintype V] [Fintype I] (c : Fin n → Bool)
    (χ : List (LitT n V)) (g : I → RGraph n) (B : List (Binding V I))
    (hs : ∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, bindingHolds c g ρ b) :
    ∃ τ, (∀ v, RegularTop (τ v)) ∧ SatT c τ χ ∧
      ∀ b ∈ B, bindingHolds c g τ b := by
  let E : List (LitT n (V ⊕ States g)) :=
    χ.map (LitT.map Sum.inl) ++
    (equations g).map (LitT.map Sum.inr) ++ B.map (bindingLit g)
  obtain ⟨ρ, hρ, hb⟩ := hs
  have hsE : ∃ ρ, SatT c ρ E := by
    refine ⟨Sum.elim ρ (values g), ?_⟩
    simp only [E, satT_append, satT_map]
    refine ⟨⟨hρ, (sat_equations c g _).mpr (values_model g)⟩, ?_⟩
    intro l hl
    obtain ⟨b, hbB, rfl⟩ := List.mem_map.mp hl
    exact (binding_spec c g _ rfl b).mpr (hb b hbB)
  have hr : SatisfiableIn RegularTop c E := by
    -- Constructor sandwiches need a child slot; nullary trees are already regular.
    cases n with
    | zero =>
      obtain ⟨σ, hσ⟩ := hsE
      exact ⟨σ, fun v => Support.Nullary.unfold_zero_surjective (σ v), hσ⟩
    | succ m => exact satisfiable_regular c hsE
  obtain ⟨τ, hc, ht⟩ := hr
  simp only [E, satT_append, satT_map] at ht
  have hv : τ ∘ Sum.inr = values g := model_unique g ((sat_equations c g _).mp ht.1.2)
  refine ⟨τ ∘ Sum.inl, fun v => hc (.inl v), ht.1.1, ?_⟩
  intro b hb
  exact (binding_spec c g τ hv b).mp (ht.2 _ (List.mem_map.mpr ⟨b, hb, rfl⟩))

end DeciENSSE.Core.Full.TopGraphs
