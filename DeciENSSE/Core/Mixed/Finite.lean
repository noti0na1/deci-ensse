import DeciENSSE.Core.Mixed.Regular
import DeciENSSE.Support.Nullary.Decide
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree

/-! # Finite realization and entailment

Finite bound pinning preserves observations and visible finite values.
Finite entailment reduces to finite satisfiability and arbitrary entailment,
with a separate enumeration of nullary labels.

## Main declarations

- `finite_bound_realization`
- `finite_class_extension`
- `decideExistsEntailsAnyFin`
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

/-- Existence of a finite-valued assignment, in the specified variance. -/
abbrev SatFin {V : Type*} (c : Fin n → Bool) (χ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop c χ

/-- At arity zero, finite satisfiability is enumeration of root labels. -/
theorem satFin_nullary_iff {V : Type*} (c : Fin 0 → Bool) (χ : List (LitT 0 V)) :
    SatFin c χ ↔ ∃ ρ : V → Sym, Nullary.satAnyB ρ χ = true := by
  constructor
  · rintro ⟨ρ, _, hρ⟩
    refine ⟨fun v => Support.Nullary.treeEquiv (ρ v), ?_⟩
    apply (Nullary.satT_ofSym_iff c _ χ).mp
    simpa only [Function.comp_def, Support.Nullary.treeEquiv,
      Equiv.coe_fn_mk, Support.Nullary.ofSym_toSym] using hρ
  · rintro ⟨ρ, hρ⟩
    exact ⟨Support.Nullary.ofSym ∘ ρ,
      fun v => Support.Nullary.toTree_zero_surjective _,
      (Nullary.satT_ofSym_iff c ρ χ).mpr hρ⟩

/-- Executable finite satisfiability at every arity. -/
def decideSatFin {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) : Decidable (SatFin c χ) := by
  cases n with
  | zero =>
    letI : Fintype Sym := ⟨{Sym.bot, Sym.f, Sym.top}, by intro s; cases s <;> simp⟩
    exact decidable_of_iff _ (satFin_nullary_iff c χ).symm
  | succ m => exact Full.decideSatFin c χ

/-- Finite bound pinning discharges every finite list of observation bounds. -/
theorem finite_bound_realization {V : Type*} (c : Fin n → Bool)
    (χ : List (LitT n V)) (hf : SatFin c χ) : BoundRealization FiniteTop c χ :=
  by
    cases n with
    | zero =>
      intro B hs
      obtain ⟨ρ, hρ, hb⟩ := hs
      exact ⟨ρ, fun v => Support.Nullary.toTree_zero_surjective (ρ v), hρ, hb⟩
    | succ m => exact finiteBoundPinningMixed c χ hf

/-- Pin both inequalities of every visible finite tree, obtaining a finite
extension that keeps the visible tuple exactly fixed. -/
theorem finite_class_extension {X Z : Type*} {c : Fin n → Bool} [Fintype X]
    {ψ : List (LitT n (X ⊕ Z))} (hf : SatFin c ψ) :
    ClassExtension FiniteTop c ψ := by
  classical
  intro ρ hρ he
  choose g hg using hρ
  let B : List (GroundBound n (X ⊕ Z)) :=
    Finset.univ.toList.flatMap fun x => [⟨.inl x, true, g x⟩, ⟨.inl x, false, g x⟩]
  obtain ⟨σ, hσ⟩ := he
  have hb : ∀ b ∈ B, b.HoldsMixed c (Sum.elim ρ σ) := by
    simp only [B, List.forall_mem_flatMap]
    intro x _
    simp [GroundBound.HoldsMixed, hg, DeciNSSE.treeLe_refl]
  obtain ⟨τ, hc, ht, hbτ⟩ := finite_bound_realization c ψ hf B ⟨_, hσ, hb⟩
  have hv (x : X) : τ (.inl x) = ρ x := by
    have hlo := hbτ ⟨.inl x, true, g x⟩ (by simp [B])
    have hhi := hbτ ⟨.inl x, false, g x⟩ (by simp [B])
    change DeciNSSE.Tree.Le c (g x).toTree (τ (.inl x)) at hlo
    change DeciNSSE.Tree.Le c (τ (.inl x)) (g x).toTree at hhi
    rw [hg x] at hlo hhi
    exact DeciNSSE.treeLe_antisymm hhi hlo
  refine ⟨fun z => τ (.inr z), fun z => hc (.inr z), ?_⟩
  have heq : Sum.elim ρ (fun z => τ (.inr z)) = τ := by
    funext v; cases v with
    | inl x => exact (hv x).symm
    | inr z => rfl
  rw [heq]; exact ht

/-- Exact finite dispatch: finite countermodels are obtained from the two
observations, and finite hidden witnesses from pinning the visible tuple. -/
theorem existsEntailsTFin_iff_mixed {X Z : Type*} [Fintype X]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ExistsEntailsTFin c φ ψ ↔
      ¬ SatFin c φ ∨ (SatFin c ψ ∧ ExistsEntailsT c φ ψ) :=
  fin_dispatch_of_transfer (fun hf => (finite_bound_realization c φ hf).observations)
    (fun hf => finite_class_extension hf)

/-- Computable finite-tree endpoint. -/
def decideExistsEntailsAnyFin {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (ExistsEntailsTFin c φ ψ) := by
  cases n with
  | zero => exact Nullary.decideExistsEntailsAnyFin c φ ψ
  | succ m =>
    letI := decideSatFin c φ
    letI := decideSatFin c ψ
    letI := decideExistsEntailsAny c φ ψ
    exact decidable_of_iff _ (existsEntailsTFin_iff_mixed c φ ψ).symm

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideSatFin_correct {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (χ : List (LitT n V)) :
    @decide _ (decideSatFin c χ) = true ↔ SatFin c χ :=
  @decide_eq_true_iff _ (decideSatFin c χ)

/-- The executable decision returns true exactly when its proposition holds. -/
theorem decideExistsEntailsAnyFin_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyFin c φ ψ) = true ↔ ExistsEntailsTFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsAnyFin c φ ψ)

/-- At arity zero the decision agrees with direct enumeration of labels. -/
theorem decideExistsEntailsAnyFin_nullary_agrees {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin 0 → Bool) (φ : List (LitT 0 X)) (ψ : List (LitT 0 (X ⊕ Z))) :
    @decide _ (decideExistsEntailsAnyFin c φ ψ) =
      @decide _ (Nullary.decideExistsEntailsAnyFin c φ ψ) := rfl

namespace FiniteMixedExamples
open LeafHornExamples ConditionsExamples

/-- The mixed-variance example has a finite solution. -/
theorem mixed_finite : SatFin arrow mixed :=
  ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩,
    by simp [SatT, HoldsT, mixed]⟩

/-- The embedded example has a finite solution. -/
theorem embedded_finite : SatFin arrow embedded :=
  ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩,
    by simp [SatT, HoldsT, embedded]⟩

/-- Finite transfer premises hold with an actual finite solution. -/
theorem transfer_nonvacuous :
    SatFin arrow mixed ∧ BoundRealization FiniteTop arrow mixed ∧
    TwoObservationRealization FiniteTop arrow mixed ∧
    ClassExtension FiniteTop arrow embedded :=
  ⟨mixed_finite, finite_bound_realization arrow mixed mixed_finite,
    (finite_bound_realization arrow mixed mixed_finite).observations,
    finite_class_extension embedded_finite⟩

/-- The same no-joint-parity ternary example in all three tree classes. -/
theorem ternary_all_classes :
    ExistsEntailsT arrow mixed embedded ∧
    ExistsEntailsTReg arrow mixed embedded ∧ ExistsEntailsTFin arrow mixed embedded :=
  ⟨embedded_entails, (existsEntailsTReg_iff_mixed _ _ _).mpr embedded_entails,
    (existsEntailsTFin_iff_mixed _ _ _).mpr (Or.inr ⟨embedded_finite, embedded_entails⟩)⟩

/-- The ternary example has no common parity assignment for both constraint systems. -/
theorem ternary_no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) :=
  embedded_no_joint_parity

/-- The decision procedure returns true on the ternary entailment example. -/
theorem ternary_positive :
    @decide _ (decideExistsEntailsAnyFin arrow mixed embedded) = true :=
  (decideExistsEntailsAnyFin_correct _ _ _).mpr ternary_all_classes.2.2

/-- The decision procedure returns false on the ternary entailment example. -/
theorem ternary_negative :
    @decide _ (decideExistsEntailsAnyFin arrow [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (existsEntailsTFin_iff_mixed _ _ _).mp
    ((decideExistsEntailsAnyFin_correct _ _ _).mp h)
  rcases he with hn | ⟨_, he⟩
  · exact hn ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩, by simp [SatT]⟩
  · exact embedded_empty_not_entails he

/-- The same unary fixed point is rejected over finite trees. -/
theorem unary_negative :
    @decide _ (decideExistsEntailsAnyFin (fun _ => true) []
      ([.lef (.inr ()) (fun _ => .inr ()), .fle (fun _ => .inr ()) (.inr ())] :
        List (LitT 1 (Unit ⊕ Unit)))) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (decideExistsEntailsAnyFin_correct _ _ _).mp h
  obtain ⟨σ, hs⟩ := he (fun _ => FTree.bot) (by simp [SatT])
  have hlo := hs (.lef (.inr ()) (fun _ => .inr ())) (by simp)
  have hhi := hs (.fle (fun _ => .inr ()) (.inr ())) (by simp)
  have hfix : σ () = FTree.node (fun _ => σ ()) :=
    FTree.toTree_injective (DeciNSSE.treeLe_antisymm hlo hhi)
  have hh := FTree.height_child_lt (fun _ : Fin 1 => σ ()) 0
  rw [← hfix] at hh
  exact (Nat.lt_irrefl _ hh)

/-- The decision procedure returns true on the nullary entailment example. -/
theorem nullary_positive :
    @decide _ (decideExistsEntailsAnyFin Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = true := by decide +kernel

/-- The decision procedure returns false on the nullary entailment example. -/
theorem nullary_negative :
    @decide _ (decideExistsEntailsAnyFin Fin.elim0 []
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = false := by decide +kernel

/-- Finite satisfiability is true on the nullary example. -/
theorem nullary_sat_positive :
    @decide _ (decideSatFin Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))) = true := by decide +kernel

/-- Finite satisfiability is false on the nullary example. -/
theorem nullary_sat_negative :
    @decide _ (decideSatFin Fin.elim0 [.bot (), .top ()]) = false := by decide +kernel

/-- Finite satisfiability is true on the ternary example. -/
theorem ternary_sat_positive :
    @decide _ (decideSatFin arrow mixed) = true :=
  (decideSatFin_correct _ _).mpr mixed_finite

end FiniteMixedExamples

end DeciENSSE.Core.Mixed
