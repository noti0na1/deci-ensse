import Mathlib.Data.List.AList
import DeciENSSE.Flattening

/-! # Subsumption of constrained type schemes

A *constrained type scheme* `S = ∀ ā. C ⇒ (Γ ⇒ τ)` has bound type variables `ā`, constraints
`C` between type expressions, a *context* `Γ`, a finite map from program variables to
expressions, and a type `τ`; its other type variables are *free*. Under a valuation `η` of
the free variables, the *instances* of `S` are the pairs `(ρ ∘ Γ, ρ(τ))` for the extensions
`ρ` of `η` to `ā` that satisfy `C`. Following Trifonov and Smith, an instance `(Δ, T)` is
below `(Δ', T')` if `T ≤ T'`, `Dom Δ ⊆ Dom Δ'` and `Δ'(v) ≤ Δ(v)` for `v ∈ Dom Δ`: contexts
are compared contravariantly. Then `S₁ ≤ S₂` if, under every valuation of the free
variables, every instance of `S₂` is above some instance of `S₁`. The valuations and the
instances range over one tree class.

The expressions of a scheme with free variables `F` and bound variables `B` are
`Term n (F ⊕ B)`, or `BFTerm n (F ⊕ B)` over `{⊥, f}`, so the bound variables of two schemes
are apart from each other and from the free ones by construction.

Subsumption is an existential entailment (`subsumesIn_iff`): if `Dom Γ₁ ⊆ Dom Γ₂`, then
`S₁ ≤ S₂` holds exactly when `C₂ ⊨ ∃ ā₁. (C₁ ∧ τ₁ ≤ τ₂ ∧ ⋀_{v ∈ Dom Γ₁} Γ₂(v) ≤ Γ₁(v))`, with
the free variables and `ā₂` visible and `ā₁` hidden; otherwise `S₁ ≤ S₂` holds exactly when
`C₂` has no solution (`subsumesIn_iff_of_not_subset`), which is the existential entailment
`C₂ ⊨ f(⊥, …, ⊥) ≤ ⊥` (`subsumesIn_iff_unsatGoal`). The deciders of `DeciENSSE.Flattening`
therefore decide subsumption in each tree class and for both signatures, and regular and
arbitrary trees agree.

## Main declarations

- `Scheme`, `SchemeInstance`, `SchemeInstance.Le`, `Scheme.inst`, `Scheme.IsInstance`.
- `SubsumesIn`: subsumption in a tree class, with `Subsumes`, `SubsumesReg`, `SubsumesFin`
  over `{⊥, f, ⊤}` and `SubsumesTopFree`, `SubsumesTopFreeReg`, `SubsumesTopFreeFin` over
  `{⊥, f}`.
- `Scheme.subsumptionGoal`: the consequent `C₁ ∧ R₁₂`.
- `subsumesIn_iff`, `subsumesIn_iff_of_not_subset`: **the subsumption formula**, in every tree
  class and at every variance; `subsumesTopFreeIn_iff` and
  `subsumesTopFreeIn_iff_of_not_subset` over `{⊥, f}`.
- `decideSubsumes`, `decideSubsumesReg`, `decideSubsumesFin`, `decideSubsumesTopFree`,
  `decideSubsumesTopFreeReg`, `decideSubsumesTopFreeFin`, with their `_correct` theorems:
  **subsumption is decidable**.
- `subsumesReg_iff`, `subsumesTopFreeReg_iff`: regular and arbitrary trees agree.
-/

namespace DeciENSSE
open DeciNSSE Flattening

variable {n : ℕ} {P T T' T₁ T₂ : Type*}

/-! ## Type schemes and their instances -/

/-- A constrained type scheme `∀ ā. C ⇒ (Γ ⇒ τ)` over the expressions `T`. The variables of
the expressions are the free and the bound type variables: `T` is `Term n (F ⊕ B)` over
`{⊥, f, ⊤}` and `BFTerm n (F ⊕ B)` over `{⊥, f}`. -/
structure Scheme (P T : Type*) where
  /-- The constraints `C`. -/
  constraint : List (TermLit T)
  /-- The context `Γ`, a finite map from the program variables `P` to expressions. -/
  context : AList fun _ : P => T
  /-- The type `τ`. -/
  type : T

/-- An instance `(Δ, T)` of a type scheme: a context `Δ`, a partial map from the program
variables to trees, and a tree `T`. -/
structure SchemeInstance (n : ℕ) (P : Type*) where
  /-- The context `Δ`. -/
  context : P → Option (Tree n)
  /-- The type `T`. -/
  type : Tree n

/-- `(Δ, T)` is below `(Δ', T')`: `T ≤ T'`, `Dom Δ ⊆ Dom Δ'`, and `Δ'(v) ≤ Δ(v)` for every
`v ∈ Dom Δ`. -/
def SchemeInstance.Le (c : Fin n → Bool) (I J : SchemeInstance n P) : Prop :=
  Tree.Le c I.type J.type ∧ (∀ v, (I.context v).isSome → (J.context v).isSome) ∧
    ∀ v t t', I.context v = some t → J.context v = some t' → Tree.Le c t' t

namespace Scheme

/-- Apply `f` to every expression of a scheme. -/
def map (f : T → T') (S : Scheme P T) : Scheme P T' where
  constraint := S.constraint.map (TermLit.map f)
  context := ⟨S.context.entries.map (Sigma.map id fun _ => f),
    List.NodupKeys.map₂ (fun _ => f) _ S.context.nodupKeys⟩
  type := f S.type

@[simp] theorem map_constraint (f : T → T') (S : Scheme P T) :
    (S.map f).constraint = S.constraint.map (TermLit.map f) := rfl

@[simp] theorem map_type (f : T → T') (S : Scheme P T) : (S.map f).type = f S.type := rfl

@[simp] theorem map_entries (f : T → T') (S : Scheme P T) :
    (S.map f).context.entries = S.context.entries.map (Sigma.map id fun _ => f) := rfl

@[simp] theorem lookup_map [DecidableEq P] (f : T → T') (S : Scheme P T) (v : P) :
    (S.map f).context.lookup v = (S.context.lookup v).map f :=
  List.dlookup_map₂ v

@[simp] theorem keys_map (f : T → T') (S : Scheme P T) :
    (S.map f).context.keys = S.context.keys :=
  List.map₂_keys _ _

variable [DecidableEq P] {F B B₁ B₂ V : Type*}

/-- The instance `(μ ∘ Γ, μ(τ))` of a scheme at an assignment `μ` of trees to its free and
bound variables. -/
def inst (S : Scheme P (Term n V)) (μ : V → Tree n) : SchemeInstance n P :=
  ⟨fun v => (S.context.lookup v).map (Term.eval μ), S.type.eval μ⟩

/-- The context of an instance is defined exactly on the domain of the context. -/
theorem isSome_inst_context (S : Scheme P (Term n V)) (μ : V → Tree n) (v : P) :
    ((S.inst μ).context v).isSome ↔ v ∈ S.context.keys := by
  simp [inst, AList.lookup_isSome, AList.mem_keys]

/-- `I` is an instance of `S` under the valuation `η` of the free variables, in the tree class
`C`: `I` is `S.inst` at the extension of `η` by trees of `C` for the bound variables that
satisfies the constraints. -/
def IsInstance (C : Tree n → Prop) (c : Fin n → Bool) (S : Scheme P (Term n (F ⊕ B)))
    (η : F → Tree n) (I : SchemeInstance n P) : Prop :=
  ∃ ρ : B → Tree n, (∀ b, C (ρ b)) ∧ TermSat c (Sum.elim η ρ) S.constraint ∧
    S.inst (Sum.elim η ρ) = I

end Scheme

/-! ## Subsumption -/

section Semantics

variable [DecidableEq P] {F B₁ B₂ : Type*}

/-- **Subsumption** `S₁ ≤ S₂` in the tree class `C`: under every valuation of the free
variables in `C`, every instance of `S₂` is above some instance of `S₁`. -/
def SubsumesIn (C : Tree n → Prop) (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Prop :=
  ∀ η : F → Tree n, (∀ x, C (η x)) → ∀ I₂, S₂.IsInstance C c η I₂ →
    ∃ I₁, S₁.IsInstance C c η I₁ ∧ I₁.Le c I₂

/-- Subsumption over arbitrary trees. -/
def Subsumes (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Prop :=
  SubsumesIn (fun _ => True) c S₁ S₂

/-- Subsumption over regular trees. -/
def SubsumesReg (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Prop :=
  SubsumesIn (fun t => ∃ g : RGraph n, g.unfold = t) c S₁ S₂

/-- Subsumption over finite trees. -/
def SubsumesFin (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Prop :=
  SubsumesIn (fun t => ∃ a : FTree n, a.toTree = t) c S₁ S₂

/-- Covariant subsumption of schemes over `{⊥, f}`, over top-free trees. -/
def SubsumesTopFree (S₁ : Scheme P (BFTerm n (F ⊕ B₁))) (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    Prop :=
  SubsumesIn TopFree (fun _ => false) (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm)

/-- Covariant subsumption of schemes over `{⊥, f}`, over top-free regular trees. -/
def SubsumesTopFreeReg (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Prop :=
  SubsumesIn (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t) (fun _ => false)
    (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm)

/-- Covariant subsumption of schemes over `{⊥, f}`, over top-free finite trees. -/
def SubsumesTopFreeFin (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Prop :=
  SubsumesIn (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t) (fun _ => false)
    (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm)

end Semantics

/-! ## The subsumption formula -/

namespace Scheme

variable [DecidableEq P] {F B₁ B₂ : Type*}

/-- The consequent `C₁ ∧ R₁₂` of the subsumption formula, for schemes whose expressions are
renamed into a common type by `r₁` and `r₂`: the constraints of `S₁`, the inequality
`τ₁ ≤ τ₂`, and `Γ₂(v) ≤ Γ₁(v)` for every `v` in both domains. -/
def goal {T : Type*} (r₁ : T₁ → T) (r₂ : T₂ → T) (S₁ : Scheme P T₁) (S₂ : Scheme P T₂) :
    List (TermLit T) :=
  S₁.constraint.map (TermLit.map r₁) ++ TermLit.le (r₁ S₁.type) (r₂ S₂.type) ::
    S₁.context.entries.filterMap fun b =>
      (S₂.context.lookup b.1).map fun t₂ => .le (r₂ t₂) (r₁ b.2)

/-- Renaming the goal renames the schemes. -/
theorem map_goal {T T₀ : Type*} (r₁ : T₁ → T) (r₂ : T₂ → T) (g : T → T₀)
    (S₁ : Scheme P T₁) (S₂ : Scheme P T₂) :
    (goal r₁ r₂ S₁ S₂).map (TermLit.map g) = goal (g ∘ r₁) (g ∘ r₂) S₁ S₂ := by
  simp only [goal, List.map_append, List.map_map, List.map_cons, List.map_filterMap,
    Option.map_map]
  congr 1
  exact List.map_congr_left fun l _ => TermLit.map_map _ _ l

/-- The goal of mapped schemes. -/
theorem goal_map {T T₀ T₀' : Type*} (r₁ : T₀ → T) (r₂ : T₀' → T) (f₁ : T₁ → T₀)
    (f₂ : T₂ → T₀') (S₁ : Scheme P T₁) (S₂ : Scheme P T₂) :
    goal r₁ r₂ (S₁.map f₁) (S₂.map f₂) = goal (r₁ ∘ f₁) (r₂ ∘ f₂) S₁ S₂ := by
  simp only [goal, map_constraint, map_type, map_entries, lookup_map, List.map_map,
    List.filterMap_map, Option.map_map]
  congr 1
  exact List.map_congr_left fun l _ => TermLit.map_map _ _ l

/-- The variables of `S₁` in the formula: free variables visible, bound variables `ā₁`
hidden. -/
def hideBound : F ⊕ B₁ → (F ⊕ B₂) ⊕ B₁ := Sum.elim (.inl ∘ .inl) .inr

/-- The consequent `C₁ ∧ R₁₂` of the subsumption formula over the visible variables `F ⊕ B₂`
and the hidden variables `B₁`. -/
def subsumptionGoal (S₁ : Scheme P (Term n (F ⊕ B₁))) (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    TermSystem n ((F ⊕ B₂) ⊕ B₁) :=
  goal (Term.map hideBound) (Term.map .inl) S₁ S₂

/-- The consequent of the subsumption formula for schemes over `{⊥, f}`. -/
def bfSubsumptionGoal (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : BFTermSystem n ((F ⊕ B₂) ⊕ B₁) :=
  goal (BFTerm.map hideBound) (BFTerm.map .inl) S₁ S₂

/-- The goal over `{⊥, f}` is the goal of the embedded schemes. -/
theorem map_bfSubsumptionGoal (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    (bfSubsumptionGoal S₁ S₂).map (TermLit.map BFTerm.toTerm) =
      subsumptionGoal (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm) := by
  rw [bfSubsumptionGoal, subsumptionGoal, map_goal, goal_map]
  congr 1 <;> funext e <;> exact BFTerm.toTerm_map _ e

/-- Satisfaction of the goal: the constraints of `S₁` hold at the hidden values `σ`, its type
is below the type of `S₂`, and so are the contexts, contravariantly, on the common domain. -/
theorem termSat_subsumptionGoal (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) (μ : F ⊕ B₂ → Tree n) (σ : B₁ → Tree n) :
    TermSat c (Sum.elim μ σ) (subsumptionGoal S₁ S₂) ↔
      TermSat c (Sum.elim (μ ∘ .inl) σ) S₁.constraint ∧
        Tree.Le c (S₁.inst (Sum.elim (μ ∘ .inl) σ)).type (S₂.inst μ).type ∧
        ∀ v t t', (S₁.inst (Sum.elim (μ ∘ .inl) σ)).context v = some t →
          (S₂.inst μ).context v = some t' → Tree.Le c t' t := by
  have hh : Sum.elim μ σ ∘ hideBound = Sum.elim (μ ∘ .inl) σ := by
    funext v; rcases v with x | b <;> rfl
  have hctx : TermSat c (Sum.elim μ σ) (S₁.context.entries.filterMap fun b =>
        (S₂.context.lookup b.1).map fun t₂ => .le (t₂.map .inl) (b.2.map hideBound)) ↔
      ∀ v t₁ t₂, S₁.context.lookup v = some t₁ → S₂.context.lookup v = some t₂ →
        Tree.Le c (t₂.eval μ) (t₁.eval (Sum.elim (μ ∘ .inl) σ)) := by
    simp only [TermSat, List.mem_filterMap, Option.map_eq_some_iff]
    constructor
    · intro h v t₁ t₂ h₁ h₂
      have := h _ ⟨⟨v, t₁⟩, AList.mem_lookup_iff.mp h₁, t₂, h₂, rfl⟩
      simpa only [TermLit.Holds, Term.eval_map, hh, Sum.elim_comp_inl] using this
    · rintro h l ⟨⟨v, t₁⟩, hb, t₂, h₂, rfl⟩
      simpa only [TermLit.Holds, Term.eval_map, hh, Sum.elim_comp_inl] using
        h v t₁ t₂ (AList.mem_lookup_iff.mpr hb) h₂
  rw [subsumptionGoal, goal, termSat_append, termSat_map, hh, termSat_cons, hctx]
  simp only [TermLit.Holds, Term.eval_map, hh, inst, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, by simpa using h₂, ?_⟩
    rintro v _ _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩
    exact h₃ v t₁ t₂ ht₁ ht₂
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, by simpa using h₂, fun v t₁ t₂ ht₁ ht₂ => h₃ v _ _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩⟩

end Scheme

open Scheme

section Formula

variable [DecidableEq P] {F B₁ B₂ : Type*} {C : Tree n → Prop} {c : Fin n → Bool}
  {S₁ : Scheme P (Term n (F ⊕ B₁))} {S₂ : Scheme P (Term n (F ⊕ B₂))}

/-- Subsumption, unfolded: every assignment of the free variables and of `ā₂` that satisfies
`C₂` has values for `ā₁` that satisfy `C₁` and give an instance below. -/
theorem subsumesIn_iff_forall :
    SubsumesIn C c S₁ S₂ ↔
      ∀ μ : F ⊕ B₂ → Tree n, (∀ v, C (μ v)) → TermSat c μ S₂.constraint →
        ∃ σ : B₁ → Tree n, (∀ b, C (σ b)) ∧ TermSat c (Sum.elim (μ ∘ .inl) σ) S₁.constraint ∧
          (S₁.inst (Sum.elim (μ ∘ .inl) σ)).Le c (S₂.inst μ) := by
  constructor
  · intro H μ hμ hs
    obtain ⟨_, ⟨σ, hσ, hs₁, rfl⟩, hle⟩ := H (μ ∘ .inl) (fun _ => hμ _) (S₂.inst μ)
      ⟨μ ∘ .inr, fun _ => hμ _, by rwa [Sum.elim_comp_inl_inr], by rw [Sum.elim_comp_inl_inr]⟩
    exact ⟨σ, hσ, hs₁, hle⟩
  · rintro H η hη _ ⟨ρ, hρ, hs, rfl⟩
    obtain ⟨σ, hσ, hs₁, hle⟩ := H (Sum.elim η ρ) (by rintro (x | b); exacts [hη x, hρ b]) hs
    exact ⟨_, ⟨σ, hσ, hs₁, rfl⟩, hle⟩

/-- **The subsumption formula, part 1.** If `Dom Γ₁ ⊆ Dom Γ₂`, then `S₁ ≤ S₂` exactly when
`C₂ ⊨ ∃ ā₁. (C₁ ∧ R₁₂)`, where the free variables and `ā₂` are visible and `ā₁` hidden, in
every tree class `C` and at every variance. -/
theorem subsumesIn_iff (hdom : S₁.context.keys ⊆ S₂.context.keys) :
    SubsumesIn C c S₁ S₂ ↔ ExistsEntailsTermIn C c S₂.constraint (subsumptionGoal S₁ S₂) := by
  rw [subsumesIn_iff_forall]
  refine forall₃_congr fun μ _ _ => exists_congr fun σ => and_congr_right fun _ => ?_
  rw [termSat_subsumptionGoal, SchemeInstance.Le]
  have hd : ∀ v, ((S₁.inst (Sum.elim (μ ∘ .inl) σ)).context v).isSome →
      ((S₂.inst μ).context v).isSome := fun v h =>
    (isSome_inst_context _ _ v).mpr (hdom ((isSome_inst_context _ _ v).mp h))
  exact ⟨fun ⟨h₁, h₂, _, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, hd, h₃⟩⟩

/-- **The subsumption formula, part 2.** If `Dom Γ₁ ⊄ Dom Γ₂`, then `S₁ ≤ S₂` exactly when
`C₂` has no solution in the tree class. -/
theorem subsumesIn_iff_of_not_subset (hdom : ¬ S₁.context.keys ⊆ S₂.context.keys) :
    SubsumesIn C c S₁ S₂ ↔ ¬ ∃ μ : F ⊕ B₂ → Tree n, (∀ v, C (μ v)) ∧ TermSat c μ S₂.constraint := by
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v, v ∈ S₁.context.keys ∧ v ∉ S₂.context.keys := by
    refine Classical.byContradiction fun h => hdom fun v hv => ?_
    by_contra hv'
    exact h ⟨v, hv, hv'⟩
  rw [subsumesIn_iff_forall]
  constructor
  · rintro H ⟨μ, hμ, hs⟩
    obtain ⟨σ, -, -, -, hd, -⟩ := H μ hμ hs
    exact hv₂ ((isSome_inst_context _ _ v).mp (hd v ((isSome_inst_context _ _ v).mpr hv₁)))
  · exact fun H μ hμ hs => absurd ⟨μ, hμ, hs⟩ H

/-- An unsatisfiable consequent with no hidden variables: `f(⊥, …, ⊥) ≤ ⊥`. -/
def unsatGoal {X : Type*} : TermSystem n (X ⊕ Empty) := [.le (.node fun _ => .bot) .bot]

/-- The same over `{⊥, f}`. -/
def bfUnsatGoal {X : Type*} : BFTermSystem n (X ⊕ Empty) := [.le (.node fun _ => .bot) .bot]

/-- A system entails the unsatisfiable consequent exactly when it has no solution. -/
theorem existsEntailsTermIn_unsatGoal_iff {X : Type*} (φ : TermSystem n X) :
    ExistsEntailsTermIn C c φ unsatGoal ↔ ¬ ∃ ρ : X → Tree n, (∀ x, C (ρ x)) ∧ TermSat c ρ φ := by
  constructor
  · rintro H ⟨ρ, hρ, hs⟩
    obtain ⟨σ, -, h⟩ := H ρ hρ hs
    simp [unsatGoal, TermLit.Holds] at h
  · exact fun H ρ hρ hs => absurd ⟨ρ, hρ, hs⟩ H

/-- Part 2 of the formula as an existential entailment. -/
theorem subsumesIn_iff_unsatGoal (hdom : ¬ S₁.context.keys ⊆ S₂.context.keys) :
    SubsumesIn C c S₁ S₂ ↔ ExistsEntailsTermIn C c S₂.constraint unsatGoal :=
  (subsumesIn_iff_of_not_subset hdom).trans (existsEntailsTermIn_unsatGoal_iff _).symm

end Formula

section FormulaTopFree

variable [DecidableEq P] {F B₁ B₂ : Type*} {C : Tree n → Prop}
  {S₁ : Scheme P (BFTerm n (F ⊕ B₁))} {S₂ : Scheme P (BFTerm n (F ⊕ B₂))}

/-- The subsumption formula over `{⊥, f}`, part 1, in every class of top-free trees. -/
theorem subsumesTopFreeIn_iff (hdom : S₁.context.keys ⊆ S₂.context.keys) :
    SubsumesIn C (fun _ => false) (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm) ↔
      ExistsEntailsTermIn C (fun _ => false) (S₂.constraint.map (TermLit.map BFTerm.toTerm))
        ((bfSubsumptionGoal S₁ S₂).map (TermLit.map BFTerm.toTerm)) := by
  rw [map_bfSubsumptionGoal]
  exact subsumesIn_iff (by simpa using hdom)

/-- The subsumption formula over `{⊥, f}`, part 2. -/
theorem subsumesTopFreeIn_iff_of_not_subset (hdom : ¬ S₁.context.keys ⊆ S₂.context.keys) :
    SubsumesIn C (fun _ => false) (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm) ↔
      ExistsEntailsTermIn C (fun _ => false) (S₂.constraint.map (TermLit.map BFTerm.toTerm))
        (bfUnsatGoal.map (TermLit.map BFTerm.toTerm)) :=
  subsumesIn_iff_unsatGoal (by simpa using hdom)

end FormulaTopFree

/-! ## Deciding subsumption -/

section Deciders

variable [DecidableEq P] {F B₁ B₂ : Type*} [Fintype F] [DecidableEq F] [Fintype B₁]
  [DecidableEq B₁] [Fintype B₂] [DecidableEq B₂]

/-- Decide subsumption over arbitrary trees. -/
@[instance_reducible] def decideSubsumes (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Decidable (Subsumes c S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesIn_iff hdom).symm (decideExistsEntailsTerm c _ _)
  else
    @decidable_of_iff _ _ (subsumesIn_iff_unsatGoal hdom).symm (decideExistsEntailsTerm c _ _)

/-- The decision returns true exactly when subsumption holds over arbitrary trees. -/
theorem decideSubsumes_correct (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    @decide _ (decideSubsumes c S₁ S₂) = true ↔ Subsumes c S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumes c S₁ S₂)

/-- Decide subsumption over regular trees. -/
@[instance_reducible] def decideSubsumesReg (c : Fin n → Bool)
    (S₁ : Scheme P (Term n (F ⊕ B₁))) (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    Decidable (SubsumesReg c S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesIn_iff hdom).symm (decideExistsEntailsTermReg c _ _)
  else
    @decidable_of_iff _ _ (subsumesIn_iff_unsatGoal hdom).symm (decideExistsEntailsTermReg c _ _)

/-- The decision returns true exactly when subsumption holds over regular trees. -/
theorem decideSubsumesReg_correct (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    @decide _ (decideSubsumesReg c S₁ S₂) = true ↔ SubsumesReg c S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumesReg c S₁ S₂)

/-- Decide subsumption over finite trees. -/
@[instance_reducible] def decideSubsumesFin (c : Fin n → Bool)
    (S₁ : Scheme P (Term n (F ⊕ B₁))) (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    Decidable (SubsumesFin c S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesIn_iff hdom).symm (decideExistsEntailsTermFin c _ _)
  else
    @decidable_of_iff _ _ (subsumesIn_iff_unsatGoal hdom).symm (decideExistsEntailsTermFin c _ _)

/-- The decision returns true exactly when subsumption holds over finite trees. -/
theorem decideSubsumesFin_correct (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) :
    @decide _ (decideSubsumesFin c S₁ S₂) = true ↔ SubsumesFin c S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumesFin c S₁ S₂)

/-- Decide covariant subsumption of schemes over `{⊥, f}`, over top-free trees. -/
@[instance_reducible] def decideSubsumesTopFree (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Decidable (SubsumesTopFree S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff hdom).symm
      (decideExistsEntailsTermTopFree S₂.constraint (bfSubsumptionGoal S₁ S₂))
  else
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff_of_not_subset hdom).symm
      (decideExistsEntailsTermTopFree S₂.constraint bfUnsatGoal)

/-- The decision returns true exactly when top-free subsumption holds. -/
theorem decideSubsumesTopFree_correct (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    @decide _ (decideSubsumesTopFree S₁ S₂) = true ↔ SubsumesTopFree S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumesTopFree S₁ S₂)

/-- Decide covariant subsumption of schemes over `{⊥, f}`, over top-free regular trees. -/
@[instance_reducible] def decideSubsumesTopFreeReg (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Decidable (SubsumesTopFreeReg S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff hdom).symm
      (decideExistsEntailsTermTopFreeReg S₂.constraint (bfSubsumptionGoal S₁ S₂))
  else
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff_of_not_subset hdom).symm
      (decideExistsEntailsTermTopFreeReg S₂.constraint bfUnsatGoal)

/-- The decision returns true exactly when top-free regular subsumption holds. -/
theorem decideSubsumesTopFreeReg_correct (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    @decide _ (decideSubsumesTopFreeReg S₁ S₂) = true ↔ SubsumesTopFreeReg S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumesTopFreeReg S₁ S₂)

/-- Decide covariant subsumption of schemes over `{⊥, f}`, over top-free finite trees. -/
@[instance_reducible] def decideSubsumesTopFreeFin (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Decidable (SubsumesTopFreeFin S₁ S₂) :=
  if hdom : S₁.context.keys ⊆ S₂.context.keys then
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff hdom).symm
      (decideExistsEntailsTermTopFreeFin S₂.constraint (bfSubsumptionGoal S₁ S₂))
  else
    @decidable_of_iff _ _ (subsumesTopFreeIn_iff_of_not_subset hdom).symm
      (decideExistsEntailsTermTopFreeFin S₂.constraint bfUnsatGoal)

/-- The decision returns true exactly when top-free finite subsumption holds. -/
theorem decideSubsumesTopFreeFin_correct (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    @decide _ (decideSubsumesTopFreeFin S₁ S₂) = true ↔ SubsumesTopFreeFin S₁ S₂ :=
  @decide_eq_true_iff _ (decideSubsumesTopFreeFin S₁ S₂)

end Deciders

/-! ## Regular and arbitrary trees agree -/

section Regular

variable [DecidableEq P] {F B₁ B₂ : Type*} [Fintype F] [Fintype B₁] [Fintype B₂]

/-- Over regular trees, the setting of Trifonov and Smith, subsumption agrees with
subsumption over arbitrary trees. -/
theorem subsumesReg_iff (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : SubsumesReg c S₁ S₂ ↔ Subsumes c S₁ S₂ := by
  by_cases hdom : S₁.context.keys ⊆ S₂.context.keys
  · rw [SubsumesReg, Subsumes, subsumesIn_iff hdom, subsumesIn_iff hdom]
    exact existsEntailsTermReg_iff c _ _
  · rw [SubsumesReg, Subsumes, subsumesIn_iff_unsatGoal hdom, subsumesIn_iff_unsatGoal hdom]
    exact existsEntailsTermReg_iff c _ _

/-- Over `{⊥, f}`, regular and arbitrary top-free trees give the same subsumption. -/
theorem subsumesTopFreeReg_iff (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : SubsumesTopFreeReg S₁ S₂ ↔ SubsumesTopFree S₁ S₂ := by
  by_cases hdom : S₁.context.keys ⊆ S₂.context.keys
  · rw [SubsumesTopFreeReg, SubsumesTopFree, subsumesTopFreeIn_iff hdom,
      subsumesTopFreeIn_iff hdom]
    exact existsEntailsTermTopFreeReg_iff _ _
  · rw [SubsumesTopFreeReg, SubsumesTopFree, subsumesTopFreeIn_iff_of_not_subset hdom,
      subsumesTopFreeIn_iff_of_not_subset hdom]
    exact existsEntailsTermTopFreeReg_iff _ _

end Regular

end DeciENSSE
