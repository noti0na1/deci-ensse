import DeciENSSE.Core.Basic
import DeciENSSE.Core.Full.Basic
import DeciENSSE.Support.Nullary.Decide

/-! # Existential entailment at arity zero

Enumerate visible and hidden assignments over the two or three root labels.
All nullary trees are finite and regular.

## Main declarations

- `entailsAnyB`, `entailsB`: finite enumeration.
- `decideExistsEntailsAny`, `decideExistsEntailsAnyReg`, `decideExistsEntailsAnyFin`.
- `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin`.
-/

namespace DeciENSSE.Core.Nullary
open DeciNSSE DeciENSSE.Core.Full

variable {V X Z : Type*}

private theorem comp_sumElim {A B D E : Type*} (f : D → E)
    (ρ : A → D) (σ : B → D) :
    f ∘ Sum.elim ρ σ = Sum.elim (f ∘ ρ) (f ∘ σ) := by
  funext v
  cases v <;> rfl

/-- Surjective presentations preserve both quantifiers of existential entailment. -/
private theorem presentation_iff {A D : Type*} (e : A → D)
    (he : Function.Surjective e) (P : (X → D) → Prop) (Q : (X ⊕ Z → D) → Prop) :
    (∀ ρ, P ρ → ∃ σ, Q (Sum.elim ρ σ)) ↔
      ∀ ρ : X → A, P (e ∘ ρ) → ∃ σ : Z → A, Q (e ∘ Sum.elim ρ σ) := by
  classical
  constructor
  · intro h ρ hρ
    obtain ⟨σ, hσ⟩ := h (e ∘ ρ) hρ
    choose τ hτ using fun z => he (σ z)
    refine ⟨τ, ?_⟩
    simpa only [comp_sumElim, show e ∘ τ = σ from funext hτ] using hσ
  · intro h ρ hρ
    choose τ hτ using fun x => he (ρ x)
    have ht : e ∘ τ = ρ := funext hτ
    obtain ⟨σ, hσ⟩ := h τ (ht.symm ▸ hρ)
    exact ⟨e ∘ σ, by simpa only [comp_sumElim, ht] using hσ⟩

/-! ## The three-element domain, with any empty variance -/

local instance : Fintype Sym where
  elems := {Sym.bot, Sym.f, Sym.top}
  complete s := by cases s <;> simp

/-- Evaluate a full literal on root labels; the empty child tuple disappears. -/
def holdsAnyB (ρ : V → Sym) : LitT 0 V → Bool
  | .le u v => decide (ρ u ≤ ρ v)
  | .fle _ u => decide (Sym.f ≤ ρ u)
  | .lef u _ => decide (ρ u ≤ Sym.f)
  | .bot u => decide (ρ u = Sym.bot)
  | .top u => decide (ρ u = Sym.top)

/-- Check every full-signature literal on root labels. -/
def satAnyB (ρ : V → Sym) (χ : List (LitT 0 V)) : Bool := χ.all (holdsAnyB ρ)

/-- Full-signature evaluation agrees with tree satisfaction. -/
theorem holdsT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Sym) (l : LitT 0 V) :
    HoldsT c (DeciENSSE.Support.Nullary.ofSym ∘ ρ) l ↔ holdsAnyB ρ l = true := by
  cases l <;>
    simp [HoldsT, holdsAnyB, Function.comp_def, DeciENSSE.Support.Nullary.leGen_zero_iff,
      ← DeciENSSE.Support.Nullary.ofSym_bot, ← DeciENSSE.Support.Nullary.ofSym_top]

/-- Full-signature conjunction evaluation agrees with satisfaction. -/
theorem satT_ofSym_iff (c : Fin 0 → Bool) (ρ : V → Sym) (χ : List (LitT 0 V)) :
    SatT c (DeciENSSE.Support.Nullary.ofSym ∘ ρ) χ ↔ satAnyB ρ χ = true := by
  simp only [SatT, satAnyB, List.all_eq_true, holdsT_ofSym_iff]

/-- Full-signature entailment reduces to finite label valuations. -/
theorem existsEntailsT_iff_labels (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsT c φ ψ ↔
      ∀ ρ : X → Sym, satAnyB ρ φ = true →
        ∃ σ : Z → Sym, satAnyB (Sum.elim ρ σ) ψ = true := by
  simp only [ExistsEntailsT, ExistsEntailsTIn, implies_true, forall_const, true_and]
  rw [presentation_iff DeciENSSE.Support.Nullary.ofSym
    DeciENSSE.Support.Nullary.treeEquiv.symm.surjective
    (fun ρ => SatT c ρ φ) (fun ρ => SatT c ρ ψ)]
  simp only [satT_ofSym_iff]

/-- A class containing every nullary tree imposes no restriction. -/
theorem existsEntailsTIn_iff (C : Tree 0 → Prop) (hC : ∀ t, C t)
    (c : Fin 0 → Bool) (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTIn C c φ ψ ↔ ExistsEntailsT c φ ψ := by
  simp [ExistsEntailsTIn, ExistsEntailsT, hC]

/-- Every nullary tree has a regular presentation. -/
theorem existsEntailsTReg_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ :=
  (Full.existsEntailsTReg_iff c φ ψ).trans
    (existsEntailsTIn_iff _ DeciENSSE.Support.Nullary.unfold_zero_surjective c φ ψ)

/-- Every nullary tree has a finite presentation. -/
theorem existsEntailsTFin_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    ExistsEntailsTFin c φ ψ ↔ ExistsEntailsT c φ ψ :=
  (Full.existsEntailsTFin_iff c φ ψ).trans
    (existsEntailsTIn_iff _ DeciENSSE.Support.Nullary.toTree_zero_surjective c φ ψ)

section FullDeciders
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Enumerate visible and hidden root-label valuations. -/
def entailsAnyB (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Bool :=
  decide (∀ ρ : X → Sym, satAnyB ρ φ = true →
    ∃ σ : Z → Sym, satAnyB (Sum.elim ρ σ) ψ = true)

/-- Label enumeration decides full-signature entailment. -/
theorem entailsAnyB_iff (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    entailsAnyB φ ψ = true ↔ ExistsEntailsT c φ ψ := by
  simpa only [entailsAnyB, decide_eq_true_eq] using (existsEntailsT_iff_labels c φ ψ).symm

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntailsAny (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsT c φ ψ) :=
  decidable_of_iff _ (entailsAnyB_iff c φ ψ)

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntailsAnyReg (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsTReg c φ ψ) :=
  decidable_of_iff _ ((entailsAnyB_iff c φ ψ).trans (existsEntailsTReg_iff c φ ψ).symm)

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntailsAnyFin (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) : Decidable (ExistsEntailsTFin c φ ψ) :=
  decidable_of_iff _ ((entailsAnyB_iff c φ ψ).trans (existsEntailsTFin_iff c φ ψ).symm)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntailsAny_correct (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAny c φ ψ) = true ↔ ExistsEntailsT c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAny c φ ψ)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntailsAnyReg_correct (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyReg c φ ψ) = true ↔ ExistsEntailsTReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyReg c φ ψ)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntailsAnyFin_correct (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyFin c φ ψ) = true ↔ ExistsEntailsTFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyFin c φ ψ)

/-- Every decision procedure for this proposition gives the same Boolean answer. -/
theorem decideExistsEntailsAny_agrees (c : Fin 0 → Bool)
    (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z)))
    (d : Decidable (ExistsEntailsT c φ ψ)) :
    @decide _ (decideExistsEntailsAny c φ ψ) = @decide _ d := by
  congr 1

end FullDeciders

/-! ## The two-element domain without top -/

/-- The two bottom–constructor trees, indexed by a Boolean. -/
def ofBool : Bool → BFTreeN 0
  | false => BFTreeN.bot
  | true => BFTreeN.node Fin.elim0

/-- A nullary constructor has the unique empty child tuple. -/
theorem bfNode_eq (a : Fin 0 → BFTreeN 0) : BFTreeN.node a = ofBool true := by
  congr 1
  funext i
  exact i.elim0

/-- Every bottom–constructor nullary tree has a Boolean label. -/
theorem ofBool_surjective : Function.Surjective ofBool := by
  intro t
  rcases BFTreeN.bot_or_node t with h | h
  · exact ⟨false, h.symm⟩
  · exact ⟨true, (h.trans (bfNode_eq _)).symm⟩

/-- Bottom–constructor comparison is Boolean implication. -/
theorem ofBool_le_iff (a b : Bool) : ofBool a ≤ ofBool b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [ofBool, BFTreeN.not_node_le_bot]

/-- The false label represents exactly bottom. -/
theorem ofBool_eq_bot_iff (a : Bool) : ofBool a = BFTreeN.bot ↔ a = false := by
  cases a
  · simp [ofBool]
  · simp only [Bool.true_eq_false, iff_false]
    intro h
    exact BFTreeN.not_node_le_bot Fin.elim0 (le_of_eq h)

/-- There are no nonempty paths at arity zero. -/
theorem word_eq_nil (w : List (Fin 0)) : w = [] := by
  cases w with
  | nil => rfl
  | cons i _ => exact i.elim0

/-- Every nullary constructor set is finite. -/
theorem isFiniteTree (t : BFTreeN 0) : IsFiniteTree t := by
  apply (Set.finite_singleton ([] : List (Fin 0))).subset
  intro w _
  exact Set.mem_singleton_iff.mpr (word_eq_nil w)

/-- Every nullary constructor set has finitely many residuals. -/
theorem isRegularTree (t : BFTreeN 0) : IsRegularTree t := by
  apply (Set.finite_singleton (t.residual []).K).subset
  rintro _ ⟨w, rfl⟩
  simp only [word_eq_nil w, Set.mem_singleton_iff]

/-- Evaluate a bottom–constructor literal on Boolean labels. -/
def holdsB (ρ : V → Bool) : Lit 0 V → Bool
  | .le u v => !ρ u || ρ v
  | .fle _ u => ρ u
  | .lef _ _ => true
  | .bot u => !ρ u

/-- Check every bottom–constructor literal on Boolean labels. -/
def satB (ρ : V → Bool) (χ : List (Lit 0 V)) : Bool := χ.all (holdsB ρ)

/-- Boolean evaluation agrees with literal satisfaction. -/
theorem holds_ofBool_iff (ρ : V → Bool) (l : Lit 0 V) :
    l.Holds (ofBool ∘ ρ) ↔ holdsB ρ l = true := by
  cases l with
  | le u v =>
    cases hu : ρ u <;> cases hv : ρ v <;>
      simp [Lit.Holds, holdsB, ofBool_le_iff, hu, hv]
  | fle a u => simp [Lit.Holds, holdsB, Function.comp_def, bfNode_eq, ofBool_le_iff]
  | lef u a => simp [Lit.Holds, holdsB, Function.comp_def, bfNode_eq, ofBool_le_iff]
  | bot u => simp [Lit.Holds, holdsB, ofBool_eq_bot_iff]

/-- Boolean conjunction evaluation agrees with satisfaction. -/
theorem sat_ofBool_iff (ρ : V → Bool) (χ : List (Lit 0 V)) :
    Sat (ofBool ∘ ρ) χ ↔ satB ρ χ = true := by
  simp only [Sat, satB, List.all_eq_true, holds_ofBool_iff]

/-- Bottom–constructor entailment reduces to Boolean valuations. -/
theorem existsEntails_iff_labels (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    ExistsEntails φ ψ ↔
      ∀ ρ : X → Bool, satB ρ φ = true →
        ∃ σ : Z → Bool, satB (Sum.elim ρ σ) ψ = true := by
  simp only [ExistsEntails, ExistsEntailsIn, implies_true, forall_const, true_and]
  rw [presentation_iff ofBool ofBool_surjective (fun ρ => Sat ρ φ) (fun ρ => Sat ρ ψ)]
  simp only [sat_ofBool_iff]

/-- A class containing every nullary constructor set imposes no restriction. -/
theorem existsEntailsIn_iff (C : BFTreeN 0 → Prop) (hC : ∀ t, C t)
    (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    ExistsEntailsIn C φ ψ ↔ ExistsEntails φ ψ := by
  simp [ExistsEntailsIn, ExistsEntails, hC]

/-- Regularity imposes no restriction at arity zero. -/
theorem existsEntailsReg_iff (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    ExistsEntailsIn IsRegularTree φ ψ ↔ ExistsEntails φ ψ :=
  existsEntailsIn_iff _ isRegularTree φ ψ

/-- Finiteness imposes no restriction at arity zero. -/
theorem existsEntailsFin_iff (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    ExistsEntailsIn IsFiniteTree φ ψ ↔ ExistsEntails φ ψ :=
  existsEntailsIn_iff _ isFiniteTree φ ψ

section BFDeciders
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Enumerate both visible and hidden Boolean assignments. -/
def entailsB (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) : Bool :=
  decide (∀ ρ : X → Bool, satB ρ φ = true →
    ∃ σ : Z → Bool, satB (Sum.elim ρ σ) ψ = true)

/-- Boolean enumeration decides bottom–constructor entailment. -/
theorem entailsB_iff (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    entailsB φ ψ = true ↔ ExistsEntails φ ψ := by
  simpa only [entailsB, decide_eq_true_eq] using (existsEntails_iff_labels φ ψ).symm

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntails (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    Decidable (ExistsEntails φ ψ) := decidable_of_iff _ (entailsB_iff φ ψ)

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntailsReg (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsRegularTree φ ψ) :=
  decidable_of_iff _ ((entailsB_iff φ ψ).trans (existsEntailsReg_iff φ ψ).symm)

/-- Decide nullary entailment by finite label enumeration. -/
def decideExistsEntailsFin (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsFiniteTree φ ψ) :=
  decidable_of_iff _ ((entailsB_iff φ ψ).trans (existsEntailsFin_iff φ ψ).symm)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntails_correct (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntails φ ψ) = true ↔ ExistsEntails φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntails φ ψ)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntailsReg_correct (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsReg φ ψ) = true ↔ ExistsEntailsIn IsRegularTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg φ ψ)

/-- The decision returns true exactly when entailment holds. -/
theorem decideExistsEntailsFin_correct (φ : List (Lit 0 X)) (ψ : List (Lit 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsFin φ ψ) = true ↔ ExistsEntailsIn IsFiniteTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin φ ψ)

end BFDeciders

end DeciENSSE.Core.Nullary
