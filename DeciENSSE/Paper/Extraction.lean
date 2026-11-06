import DeciENSSE.Core.Mixed.Extract
import DeciENSSE.Core.Mixed.ExtractModel
import DeciENSSE.Core.Words.Self.NonMortal

/-! # Paper contract: Two-Word Holes with Self Events

Contract entries for the section *Two-Word Holes with Self Events* (`sec:ex`): head events
end before the first rejected cut, the extracted instances have forced target heads, and,
under (U), condition (II) fails exactly when an extracted instance has a hole, whose
closure gives a countermodel (`thm:ex-reduction`, `cor:ex-entailment`).
-/
namespace DeciENSSE.Paper
open Core.Full Core.Mixed Core.Words
variable {n : ℕ} {X Z : Type*}

/-- **Lemma (Heads end before the first rejected cut)**, `lem:ex-head-before-J`.
Form: J is an option; its defined value is supplied as an equality. The alphabet need not be finite.
-/
theorem lem_ex_head_before_J {α SA SB SC SD : Type*}
    [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
    [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]
    (I : Self.SelfTwoWordInstance α SA SB SC SD) {u t : Word α} {s e j : ℕ}
    (hf : I.ForcedHeads) (hh : I.HeadEvent u t s e) (hj : I.J t = some j) :
    e ≤ j ∧ (t.drop j).IsSuffix (t.drop e) := by
  have h := I.toTwoWordInstance.head_cut_le_J hf hh hj
  exact ⟨h, List.drop_suffix_drop_left t h⟩

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-- **Lemma (Forced target heads)**, `lem:ex-fh`.
-/
theorem lem_ex_fh (p q : X × Bool) : (extractSelf c φ ψ p q).ForcedHeads :=
  extractSelf_forcedHeads p q

/-- **Theorem (Holes and condition (II))**, `thm:ex-reduction`(1).
Form: This item includes the theorem's unnumbered pointwise equivalence; signed variables are pairs and visible variables use Sum.inl.
-/
theorem thm_ex_reduction_1 (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ) :
    (∀ (p q : X × Bool) (u t : List (Fin n)),
      (extractSelf c φ ψ p q).IsHole u t ↔
        Live c φ (p.1, p.2, t) ∧
        Moves c ψ (.inl p.1, p.2, t) (.inl q.1, q.2, u) ∧
        (q.1, q.2, u) ∉ Cl c φ (p.1, p.2, t)) ∧
    (CondII c φ ψ ↔ ∀ p q, ¬ (extractSelf c φ ψ p q).HasHole) :=
  ⟨fun p q => extractSelf_isHoleS_iff p q hφ hU,
    condII_iff_no_holes hφ hU⟩

/-- **Theorem (Holes and condition (II))**, `thm:ex-reduction`(2).
Form: Models are sets of signed atoms; `restrict` restricts a model to the visible variables and `configSet` is the atom set of an assignment.
-/
theorem thm_ex_reduction_2 (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    {p q : X × Bool} {u t : List (Fin n)} (hh : (extractSelf c φ ψ p q).IsHole u t) :
    (¬ ∃ T, Sol c ψ T ∧ restrict T = Cl c φ (p.1, p.2, t)) ∧
      ∃ ρ, SatT c ρ φ ∧ configSet c ρ = Cl c φ (p.1, p.2, t) ∧
        ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ :=
  ⟨extractSelf_hole_not_projected hφ hU hh, (extractSelf_hole_countermodel hφ hU hh).2⟩

/-- **Corollary (Entailment and holes)**, `cor:ex-entailment`.
-/
theorem cor_ex_entailment (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧
      ∀ p q, ¬ (extractSelf c φ ψ p q).HasHole :=
  mixed_reduction hφ hψ
end DeciENSSE.Paper
