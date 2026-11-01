import DeciENSSE.Core.Full.Basic
import DeciENSSE.Support.Graphs
import DeciNSSE.Constraints.Basic
import DeciNSSE.Satisfiability.FiniteVariance
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Tree

/-! # Eliminating variable inequalities by constructor sandwiches

The input is already a flat conjunction. This translation eliminates each
variable inequality using two constructor bounds with a shared fresh witness;
it does not flatten nested input terms. The distinguished child requires
`NeZero n`. Finite and regular solutions transfer through these sandwiches.

## Main declarations

- `Flatten.flatten`
- `Flatten.forward`
- `Flatten.backward`
- `decideSatFin`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace Flatten

variable [NeZero n]

/-- Original variables together with a fresh witness for each ordered pair. -/
abbrev Vars (V : Type*) := V ⊕ (V × V)

/-- The distinguished child is slot zero; all other children share a filler. -/
def sandwichArgs {A : Type*} (head filler : A) (i : Fin n) : A :=
  if i = 0 then head else filler

/-- Mapping children preserves the distinguished child and shared filler. -/
@[simp] theorem comp_sandwichArgs {A B : Type*} (f : A → B) (a b : A) :
    f ∘ sandwichArgs (n := n) a b = sandwichArgs (f a) (f b) := by
  funext i
  by_cases hi : i = 0 <;> simp [sandwichArgs, hi]

/-- Both polarities of slot zero encode the same original inequality.
Off-spine children impose only reflexivity, at any variance. -/
theorem sandwich_iff (c : Fin n → Bool) (u v : DeciNSSE.Tree n) :
    DeciNSSE.Tree.Le c
      (DeciNSSE.Tree.node (sandwichArgs (if c 0 then v else u) u))
      (DeciNSSE.Tree.node (sandwichArgs (if c 0 then u else v) u)) ↔ DeciNSSE.Tree.Le c u v := by
  rw [DeciNSSE.node_treeLe_node_iff]
  constructor
  · intro h
    have h0 := h 0
    cases hc : c 0 <;> simpa [sandwichArgs, hc] using h0
  · intro h i
    by_cases hi : i = 0
    · subst i
      cases hc : c 0 <;> simpa [sandwichArgs, hc] using h
    · simp [sandwichArgs, hi, DeciNSSE.treeLe_refl]

/-- A shared sandwich witness for each ordered pair. At arity one no
filler slot remains. At negative slot-zero variance the endpoints swap. -/
def literal {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k) :
    LitT n V → Constraint n k
  | .le u v =>
      [.fLe (sandwichArgs (e (.inl (if c 0 then v else u))) (e (.inl u)))
          (e (.inr (u,v))),
       .leF (e (.inr (u,v)))
          (sandwichArgs (e (.inl (if c 0 then u else v))) (e (.inl u)))]
  | .fle a u => [.fLe (fun i => e (.inl (a i))) (e (.inl u))]
  | .lef u a => [.leF (e (.inl u)) (fun i => e (.inl (a i)))]
  | .bot u => [.eqBot (e (.inl u))]
  | .top u => [.eqTop (e (.inl u))]

/-- Concatenate the flat translations of all literals. -/
def flatten {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (χ : List (LitT n V)) := χ.flatMap (literal c e)

/-- Extend a valuation by the constructor witnesses for its variable comparisons. -/
def extend {V : Type*} (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n) : Vars V → DeciNSSE.Tree n :=
  Sum.elim ρ (fun p => DeciNSSE.Tree.node
    (sandwichArgs (ρ (if c 0 then p.2 else p.1)) (ρ p.1)))

/-- A satisfied literal yields a satisfied flat translation. -/
theorem literal_forward {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (ρ : V → DeciNSSE.Tree n) {l : LitT n V} (h : HoldsT c ρ l) :
    DeciNSSE.Sat c (extend c ρ ∘ e.symm) (literal c e l) := by
  cases l with
  | le u v =>
    change DeciNSSE.Tree.Le c (ρ u) (ρ v) at h
    cases hc : c 0 <;>
      simpa [literal, DeciNSSE.Sat, Lit.holds, extend, hc, DeciNSSE.treeLe_refl]
        using (sandwich_iff c (ρ u) (ρ v)).mpr h
  | fle a u => simpa [literal, DeciNSSE.Sat, Lit.holds, extend,
      HoldsT, Function.comp_def] using h
  | lef u a => simpa [literal, DeciNSSE.Sat, Lit.holds, extend,
      HoldsT, Function.comp_def] using h
  | bot u => simpa [literal, DeciNSSE.Sat, Lit.holds, extend, HoldsT] using h
  | top u => simpa [literal, DeciNSSE.Sat, Lit.holds, extend, HoldsT] using h

/-- A satisfied flat translation yields the original literal. -/
theorem literal_backward {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (τ : Fin k → DeciNSSE.Tree n) {l : LitT n V} (h : DeciNSSE.Sat c τ (literal c e l)) :
    HoldsT c (fun v => τ (e (.inl v))) l := by
  cases l with
  | le u v =>
    simp only [literal, DeciNSSE.Sat, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Lit.holds, comp_sandwichArgs] at h
    have hh := DeciNSSE.treeLe_trans h.1 h.2
    have hh' := (DeciNSSE.node_treeLe_node_iff c _ _).mp hh 0
    cases hc : c 0 <;> simpa [HoldsT, sandwichArgs, hc] using hh'
  | fle a u => simpa [literal, DeciNSSE.Sat, Lit.holds, HoldsT,
      Function.comp_def] using h
  | lef u a => simpa [literal, DeciNSSE.Sat, Lit.holds, HoldsT,
      Function.comp_def] using h
  | bot u => simpa [literal, DeciNSSE.Sat, Lit.holds, HoldsT] using h
  | top u => simpa [literal, DeciNSSE.Sat, Lit.holds, HoldsT] using h

/-- Extend a solution to the flattened constraints. -/
theorem forward {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    {ρ : V → DeciNSSE.Tree n} {χ : List (LitT n V)} (h : SatT c ρ χ) :
    DeciNSSE.Sat c (extend c ρ ∘ e.symm) (flatten c e χ) := by
  intro l hl
  obtain ⟨l', hl', hl⟩ := List.mem_flatMap.mp hl
  exact literal_forward c e ρ (h l' hl') l hl

/-- Restrict a flattened solution to the original constraints. -/
theorem backward {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    {τ : Fin k → DeciNSSE.Tree n} {χ : List (LitT n V)}
    (h : DeciNSSE.Sat c τ (flatten c e χ)) :
    SatT c (fun v => τ (e (.inl v))) χ := by
  intro l hl
  exact literal_backward c e τ (fun l' hl' => h l' (List.mem_flatMap.mpr ⟨l, hl, hl'⟩))

/-- Flattening preserves and reflects finite satisfiability. -/
theorem finite_iff {V : Type*} {k : ℕ} (c : Fin n → Bool) (e : Vars V ≃ Fin k)
    (χ : List (LitT n V)) :
    SatisfiableIn (fun t => ∃ g : FTree n, g.toTree = t) c χ ↔
      ∃ τ : Fin k → FTree n, DeciNSSE.Sat c (FTree.toTree ∘ τ) (flatten c e χ) := by
  classical
  constructor
  · rintro ⟨ρ, hc, hs⟩
    choose g hg using hc
    let τ : Fin k → FTree n := Sum.elim g (fun p => FTree.node
      (sandwichArgs (g (if c 0 then p.2 else p.1)) (g p.1))) ∘ e.symm
    refine ⟨τ, ?_⟩
    have he : FTree.toTree ∘ τ = extend c ρ ∘ e.symm := by
      funext i
      change (Sum.elim g (fun p => FTree.node
        (sandwichArgs (g (if c 0 then p.2 else p.1)) (g p.1))) (e.symm i)).toTree = _
      cases he : e.symm i <;> simp [extend, hg, Function.comp_apply, he]
      funext j
      by_cases hj : j = 0 <;> simp [sandwichArgs, hj, hg]
    rw [he]
    exact forward c e hs
  · rintro ⟨τ, hτ⟩
    exact ⟨fun v => (τ (e (.inl v))).toTree, fun v => ⟨_, rfl⟩, backward c e hτ⟩

end Flatten

/-- Regular satisfiability via variance-aware sandwich elimination. -/
theorem satisfiable_regular [NeZero n] {V : Type*} [Fintype V] (c : Fin n → Bool)
    {χ : List (LitT n V)} (h : ∃ ρ, SatT c ρ χ) :
    SatisfiableIn (fun t => ∃ g : RGraph n, g.unfold = t) c χ := by
  let e := Fintype.equivFin (Flatten.Vars V)
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨τ, hτ⟩ := (Support.Graphs.satReg_iff_sat c (Flatten.flatten c e χ)).mpr
    ⟨_, Flatten.forward c e hρ⟩
  exact ⟨fun v => (τ (e (.inl v))).unfold, fun v => ⟨_, rfl⟩,
    Flatten.backward c e hτ⟩

/-- Existence of a finite-valued assignment at the specified variance. -/
abbrev SatFin {V : Type*} (c : Fin n → Bool) (χ : List (LitT n V)) : Prop :=
  SatisfiableIn (fun t => ∃ g : FTree n, g.toTree = t) c χ

/-- Executable finite satisfiability, including variable inequalities. -/
def decideSatFin [NeZero n] {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) : Decidable (SatFin c χ) :=
  (Fintype.truncEquivFin (Flatten.Vars V)).recOnSubsingleton fun e =>
    decidable_of_iff (DeciNSSE.satFinB c (Flatten.flatten c e χ) = true)
      ((DeciNSSE.satFinB_iff c _).trans (Flatten.finite_iff c e χ).symm)

end DeciENSSE.Core.Full
