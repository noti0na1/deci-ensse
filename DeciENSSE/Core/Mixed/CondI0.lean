import DeciENSSE.Core.Mixed.Sat

/-! # Computable condition (I0) for mixed systems

Endpoint-preserving loop deletion bounds failures of the positive unit
condition, giving a finite decision procedure at every arity.

## Main declarations

- `FailureI0`, `failureI0_short`, `condI0_bounded`,
  `decideCondI0`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words

variable {n : ℕ}
open DeciENSSE.Core.Full

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-- A consequent unit hit with no antecedent unit hit, on one visible atom. -/
def FailureI0 (p : X × Bool) (w : List (Fin n)) : Prop :=
  ((muDFA c ψ (.inl p.1, p.2)).run w).2 = true ∧
    ¬ ((muDFA c φ p).run w).2 = true

/-- The finite predicate has a computable decision. -/
instance (p : X × Bool) (w : List (Fin n)) : Decidable (FailureI0 c φ ψ p w) := by
  unfold FailureI0; infer_instance

/-- A failure is consequent unit membership without antecedent unit membership. -/
theorem failureI0_iff (p : X × Bool) (w : List (Fin n)) :
    FailureI0 c φ ψ p w ↔
      (.inl p.1, p.2, w) ∈ Mu c ψ ∧ (p.1, p.2, w) ∉ Mu c φ := by
  simp only [FailureI0, muDFA_accept]

/-- The product state count, including both sticky flags. -/
def condI0Bound (X Z : Type*) [Fintype X] [Fintype Z] : ℕ :=
  Fintype.card (MuState (X ⊕ Z) × MuState X)

/-- Endpoint-preserving loop deletion preserves both positive and negative tests. -/
theorem failureI0_short {p : X × Bool} {w : List (Fin n)} (h : FailureI0 c φ ψ p w) :
    ∃ u, u.length < condI0Bound X Z ∧ FailureI0 c φ ψ p u := by
  let M := (muDFA c ψ (.inl p.1, p.2)).prod (muDFA c φ p)
  obtain ⟨u, hu, _, he⟩ := M.short_safe_path (fun _ => True) M.start w
    ((M.pathSafe_iff _ _ _).mpr (by simp))
  change M.run u = M.run w at he
  have hh : (M.run w).1.2 = true ∧ ¬ (M.run w).2.2 = true := by
    simpa only [M, LDFA.prod_run, FailureI0] using h
  refine ⟨u, hu, ?_⟩
  rw [← he] at hh
  simpa only [M, LDFA.prod_run, FailureI0] using hh

/-- The positive unit condition fails exactly when some failure exists. -/
theorem not_condI0_iff : ¬ CondI0 c φ ψ ↔ ∃ p w, FailureI0 c φ ψ p w := by
  classical
  simp only [CondI0, Set.subset_def, not_forall]
  constructor
  · rintro ⟨⟨x, s, w⟩, hψ, hφ⟩
    exact ⟨(x, s), w, (failureI0_iff c φ ψ (x, s) w).mpr ⟨hψ, hφ⟩⟩
  · rintro ⟨⟨x, s⟩, w, hh⟩
    obtain ⟨hψ, hφ⟩ := (failureI0_iff c φ ψ (x, s) w).mp hh
    exact ⟨(x, s, w), hψ, hφ⟩

/-- The universal condition is equivalent to a finite search with no failures. -/
theorem condI0_bounded : CondI0 c φ ψ ↔
    ¬ ∃ p, ∃ w ∈ wordsUpTo (condI0Bound X Z), FailureI0 c φ ψ p w := by
  classical
  rw [← not_iff_not, not_condI0_iff, not_not]
  constructor
  · rintro ⟨p, w, hh⟩
    obtain ⟨u, hu, hh⟩ := failureI0_short c φ ψ hh
    exact ⟨p, u, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hu), hh⟩
  · rintro ⟨p, w, _, hh⟩
    exact ⟨p, w, hh⟩

/-- Executable (I0), with no satisfiability hypothesis. -/
def decideCondI0 : Decidable (CondI0 c φ ψ) :=
  decidable_of_iff
    (¬ ∃ p, ∃ w ∈ wordsUpTo (condI0Bound X Z), FailureI0 c φ ψ p w)
    (condI0_bounded c φ ψ).symm

/-- The positive-unit decision returns true exactly when the condition holds. -/
theorem decideCondI0_true_iff :
    @decide (CondI0 c φ ψ) (decideCondI0 c φ ψ) = true ↔ CondI0 c φ ψ :=
  @decide_eq_true_iff _ (decideCondI0 c φ ψ)

end DeciENSSE.Core.Mixed
