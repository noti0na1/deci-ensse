import DeciENSSE.Core.Automata

/-! # Finite tests for forced atoms and liveness

The lower automata detect visible atoms forced by the consequent but not the
antecedent. The upper automata detect a seed that is live in the antecedent
but reaches a forbidden consequent root. A product of the two powerset state
spaces bounds the length of either witness, so finite word searches decide
(I0) and liveness preservation.

This completes the first two tests in the covariant condition step. The
remaining condition (II) is reduced to two-word instances in `Core/Reduction`.
The liveness test assumes that both systems are satisfiable; satisfiability
is decided separately by `Automata.decideSat`.

## Main declarations

- `Automata.FailureI0`, `Automata.FailureLive`: automaton witnesses of failure.
- `Automata.condI0_bounded`, `Automata.condLive_bounded`: bounded characterizations.
- `Automata.decideCondI0`, `Automata.decideCondLive`: executable condition tests.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Automata
variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A uniform bound 2^(2ν), where ν counts all visible and hidden variables. -/
def witnessBound (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  2 ^ (2 * (Fintype.card X + Fintype.card Z))

omit [DecidableEq X] [DecidableEq Z] in
/-- The joint powerset state count is bounded by the combined variable count. -/
theorem product_card_le : Fintype.card (Finset X × Finset (X ⊕ Z)) ≤ witnessBound X Z := by
  simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_sum, witnessBound]
  rw [← Nat.pow_add]
  apply Nat.pow_le_pow_right (by omega)
  omega

/-- A final-state witness to failure of the forced-atom condition (I0). -/
def FailureI0 (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) (x : X) (w : List (Fin n)) : Prop :=
  (Q ψ (.inl x) w ∩ LowF ψ).Nonempty ∧ Disjoint (Q φ x w) (LowF φ)

/-- A safe-path witness to failure of the liveness condition. -/
def FailureLive (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) (x : X) (w : List (Fin n)) : Prop :=
  Safe φ x w ∧ (P ψ (.inl x) w ∩ Bot ψ).Nonempty

instance {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))} {x : X} {w : List (Fin n)} :
    Decidable (FailureI0 φ ψ x w) := by unfold FailureI0; infer_instance
instance {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))} {x : X} {w : List (Fin n)} :
    Decidable (FailureLive φ ψ x w) := by unfold FailureLive; infer_instance

/-- Failure of the forced-atom condition (I0) has an automaton witness. -/
theorem not_condI0_iff (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ¬ CondI0 φ ψ ↔ ∃ x w, FailureI0 φ ψ x w := by
  classical
  simp only [CondI0, Set.subset_def, not_forall]
  constructor
  · rintro ⟨⟨x, w⟩, hψ, hφ⟩
    exact ⟨x, w, mu_membership.mp hψ,
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp
        (fun h => hφ (mu_membership.mpr h)))⟩
  · rintro ⟨x, w, hψ, hφ⟩
    exact ⟨(x, w), mu_membership.mpr hψ, fun h =>
      Finset.disjoint_left.mp hφ (Finset.mem_inter.mp (mu_membership.mp h).choose_spec).1
        (Finset.mem_inter.mp (mu_membership.mp h).choose_spec).2⟩

/-- Witness failure of the liveness condition by cutting a dead word at a bottom hit. -/
theorem not_condLive_iff {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    (hφ : ∃ ρ, Sat ρ φ) (hψ : ∃ ρ, Sat ρ ψ) :
    ¬ CondLive φ ψ ↔ ∃ x w, FailureLive φ ψ x w := by
  classical
  simp only [CondLive, Set.subset_def, not_forall]
  constructor
  · rintro ⟨⟨x, w⟩, h, hn⟩
    have hs := (liveness hφ x w).mp h
    have hns : ¬ Safe ψ (.inl x) w := fun h => hn ((liveness hψ (.inl x) w).mpr h)
    rw [safe_iff] at hns
    push Not at hns
    obtain ⟨j, hj, hb⟩ := hns
    exact ⟨x, w.take j, safe_prefix hs (List.take_prefix j w),
      Finset.not_disjoint_iff_nonempty_inter.mp hb⟩
  · rintro ⟨x, w, hs, hb⟩
    refine ⟨(x, w), (liveness hφ x w).mpr hs, ?_⟩
    intro h
    have hsafe := (safe_iff ψ (.inl x) w).mp ((liveness hψ (.inl x) w).mp h) w.length le_rfl
    simp only [List.take_length] at hsafe
    exact (Finset.not_disjoint_iff_nonempty_inter.mpr hb) hsafe

/-- The lower product preserves both final tests under loop deletion. -/
theorem failureI0_short {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    {x : X} {w : List (Fin n)} (h : FailureI0 φ ψ x w) :
    ∃ v, v.length < witnessBound X Z ∧ FailureI0 φ ψ x v := by
  let M := (lower φ x).prod (lower ψ (.inl x))
  have hs : M.PathSafe (fun _ => True) M.start w :=
    (LDFA.pathSafe_iff _ _ _ _).mpr (fun _ _ => trivial)
  obtain ⟨v, hv, _, he⟩ := M.short_safe_path (fun _ => True) M.start w hs
  have hp : (Q φ x v, Q ψ (.inl x) v) = (Q φ x w, Q ψ (.inl x) w) := by
    change M.run v = M.run w at he
    simpa only [M, LDFA.prod_run, Q] using he
  refine ⟨v, hv.trans_le product_card_le, ?_⟩
  have h₁ := congrArg Prod.fst hp
  have h₂ := congrArg Prod.snd hp
  change Q φ x v = Q φ x w at h₁
  change Q ψ (.inl x) v = Q ψ (.inl x) w at h₂
  simpa only [FailureI0, h₁, h₂] using h

/-- The upper product retains the safety restriction on its first component. -/
theorem failureLive_short {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    {x : X} {w : List (Fin n)} (h : FailureLive φ ψ x w) :
    ∃ v, v.length < witnessBound X Z ∧ FailureLive φ ψ x v := by
  let M := (upper φ x).prod (upper ψ (.inl x))
  let G : Finset X × Finset (X ⊕ Z) → Prop := fun p => Disjoint p.1 (Bot φ)
  have safe_eq (v : List (Fin n)) : M.PathSafe G M.start v ↔ Safe φ x v := by
    rw [LDFA.pathSafe_iff, safe_iff]
    change (∀ j ≤ v.length, Disjoint (M.run (v.take j)).1 (Bot φ)) ↔ _
    simp only [M, LDFA.prod_run, P]
  obtain ⟨v, hv, hs, he⟩ := M.short_safe_path G M.start w ((safe_eq w).mpr h.1)
  have hp : (P φ x v, P ψ (.inl x) v) = (P φ x w, P ψ (.inl x) w) := by
    change M.run v = M.run w at he
    simpa only [M, LDFA.prod_run, P] using he
  have h₂ : P ψ (.inl x) v = P ψ (.inl x) w := congrArg Prod.snd hp
  exact ⟨v, hv.trans_le product_card_le, (safe_eq v).mp hs,
    by simpa only [h₂] using h.2⟩

/-- An executable enumeration of all arity-n words strictly shorter than B. -/
def BoundedWitness (B : ℕ) (F : List (Fin n) → Prop) : Prop :=
  ∃ m : Fin B, ∃ letters : Fin m.val → Fin n, F (List.ofFn letters)

instance {B : ℕ} {F : List (Fin n) → Prop} [DecidablePred F] : Decidable (BoundedWitness B F) := by
  unfold BoundedWitness; infer_instance

/-- Finite-function enumeration agrees with the word-length bound. -/
theorem boundedWitness_iff (B : ℕ) (F : List (Fin n) → Prop) :
    BoundedWitness B F ↔ ∃ w, w.length < B ∧ F w := by
  constructor
  · rintro ⟨n, letters, h⟩
    exact ⟨List.ofFn letters, by simp, h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w.length, hw⟩, fun i => w[i], by simpa using h⟩

/-- The proved finite witness bound for `CondI0`. -/
theorem condI0_bounded (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    CondI0 φ ψ ↔ ¬ ∃ x, BoundedWitness (witnessBound X Z) (FailureI0 φ ψ x) := by
  classical
  rw [← not_iff_not, not_condI0_iff, not_not]
  constructor
  · rintro ⟨x, w, h⟩
    exact ⟨x, (boundedWitness_iff _ _).mpr (failureI0_short h)⟩
  · rintro ⟨x, h⟩
    obtain ⟨w, _, hw⟩ := (boundedWitness_iff _ _).mp h
    exact ⟨x, w, hw⟩

/-- The finite witness bound for liveness preservation in two satisfiable systems. -/
theorem condLive_bounded {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    (hφ : ∃ ρ, Sat ρ φ) (hψ : ∃ ρ, Sat ρ ψ) :
    CondLive φ ψ ↔ ¬ ∃ x, BoundedWitness (witnessBound X Z) (FailureLive φ ψ x) := by
  classical
  rw [← not_iff_not, not_condLive_iff hφ hψ, not_not]
  constructor
  · rintro ⟨x, w, h⟩
    exact ⟨x, (boundedWitness_iff _ _).mpr (failureLive_short h)⟩
  · rintro ⟨x, h⟩
    obtain ⟨w, _, hw⟩ := (boundedWitness_iff _ _).mp h
    exact ⟨x, w, hw⟩

/-- Executable decider for condition `CondI0`; no satisfiability proof is needed. -/
def decideCondI0 (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Decidable (CondI0 φ ψ) :=
  decidable_of_iff (¬ ∃ x, BoundedWitness (witnessBound X Z) (FailureI0 φ ψ x))
    (condI0_bounded φ ψ).symm

/-- Executable decider for condition `CondLive` for two satisfiable systems. -/
def decideCondLive (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z)))
    (hφ : ∃ ρ, Sat ρ φ) (hψ : ∃ ρ, Sat ρ ψ) : Decidable (CondLive φ ψ) :=
  decidable_of_iff (¬ ∃ x, BoundedWitness (witnessBound X Z) (FailureLive φ ψ x))
    (condLive_bounded hφ hψ).symm

end Automata

end DeciENSSE.Core
