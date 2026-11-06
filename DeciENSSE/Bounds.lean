import DeciENSSE.Bounds.Estimates
import DeciENSSE.Bounds.States
import DeciENSSE.Core.Mixed.Units
import DeciENSSE.Core.Words.Self.Bound
import DeciENSSE.TopFree

/-! # Counterexample bounds in the number of variables

Let `φ` be a flat system over the visible variables `X` and `ψ` a flat system over `X ⊕ Z`,
with `v = |X|` and `s = |X| + |Z|`. When the entailment `φ ⊨ ∃ Z. ψ` fails over arbitrary
trees, one of three conditions fails, and each failure has a witness word whose length is
bounded in `v` and `s` alone, independently of the arity and the variance:

- an (I)-word, of length less than `2^(2v+2s+2)` (`prop:as-bounds`(1));
- a (U)-word, of length at most `holeBound(N_U, d_{N_U}) ≤ E₃(10v + 10s + 17)`
  (`thm:un-decidable`, `prop:as-bounds`(2));
- a hole of an extracted instance, of length at most `Lnm(N_A, N_B, N_{A'}, N_{B'})`, or a
  mortal hole whose separator word has length at most `Len♯_{I_pq} ≤ E₃(10v + 12s + 15)`
  (`cor:mo-extracted`, `prop:as-bounds`(3)).

If `v ≥ 1`, each of these bounds is at most `E₃(10v + 12s + 15) ≤ E₃(22s + 15)`; if `v = 0`,
no condition fails. Over `{⊥, f}` the gadget of `DeciENSSE.TopFree` doubles `v` and `s`,
which gives `E₃(20v + 24s + 15) ≤ E₃(44s + 15)` (`cor:tc-bf`, `thm:as-main`(4)).

The witnesses are the existing ones of the decision procedure: failures of (I0) as
membership in `μ`, live words with `DeadU`, and holes of `extractSelf`. The bounds are over
arbitrary trees; the regular and finite classes reduce to them by
`DeciENSSE.Core.Mixed.existsEntailsTReg_iff_mixed` and
`DeciENSSE.Core.Mixed.existsEntailsTFin_iff_mixed`.

## Main declarations

- `exists_short_hole_or_mortalHole`: short holes of instances with arbitrary finite state
  types (`cor:nm-short-holes` with `thm:mo-short`).
- `unitHoleBound_le`, `not_condU_iff_short`: condition (U) (`thm:un-decidable`).
- `extracted_mortalHoleBound_le`, `exists_short_extracted_mortalHole`: `cor:mo-extracted`.
- `not_condI0_iff_short`, `exists_short_extracted_hole`, `counterexampleBounds_le`,
  `conditions_of_isEmpty`: `prop:as-bounds`.
- `exists_short_failure`: the bound part of `thm:as-main`(3) over arbitrary trees.
- `card_gadget_vars`, `gadget_bound`, `exists_short_failure_gadget`: `cor:tc-bf` and the
  bound part of `thm:as-main`(4).

The declarations are in the namespace `DeciENSSE.Bounds`.
-/

namespace DeciENSSE.Bounds
open DeciENSSE.Core.Mixed DeciENSSE.Core.Words DeciENSSE.Core.Words.Self
  DeciENSSE.Core.Full DeciNSSE.Holes DeciNSSE.RejectedTail

/-! ## Short holes of two-word instances with arbitrary state types -/

section Instances
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {SA SB SC SD : Type*} [Fintype SA] [Fintype SB] [Fintype SC] [Fintype SD]
  [DecidableEq SA] [DecidableEq SB] [DecidableEq SC] [DecidableEq SD]

/-- **Short holes** (`cor:nm-short-holes` with `thm:mo-short`), for arbitrary finite state
types: an instance with (FH) and a hole has a hole `(u, t)` with
`|u| + |t| ≤ Lnm(N_A, N_B, N_{A'}, N_{B'})`, or a mortal hole whose separator word has length
`|u| + 1 + |t| ≤ Len♯_I`. The state counts are those of the given types. -/
theorem exists_short_hole_or_mortalHole (I : SelfTwoWordInstance α SA SB SC SD)
    (hfh : I.ForcedHeads) (hh : I.HasHole) :
    ∃ u t, I.IsHole u t ∧
      (u.length + t.length ≤ pumpHoleBound (Fintype.card SA) (Fintype.card SB)
          (Fintype.card SC) (Fintype.card SD) ∨
        (I.IsMortalHole u t ∧ u.length + t.length + 1 ≤ Mortal.mortalHoleBound
          (Fintype.card SA) (Fintype.card SB) (Fintype.card SC) (Fintype.card SD))) := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    have empty (w : Word α) : w = [] := by
      cases w with
      | nil => rfl
      | cons x _ => exact isEmptyElim x
    obtain ⟨u, t, ht⟩ := hh
    exact ⟨u, t, ht, Or.inl (by simp [empty u, empty t])⟩
  | inr h =>
    have := Classical.inhabited_of_nonempty h
    let a := Fintype.equivFin SA
    let b := Fintype.equivFin SB
    let c := Fintype.equivFin SC
    let d := Fintype.equivFin SD
    rcases ((I.rename a b c d).three_cases
        ((SelfTwoWordInstance.rename_forcedHeads I a b c d).mpr hfh)).mp
        ((SelfTwoWordInstance.rename_hasHole I a b c d).mpr hh) with hn | hm
    · obtain ⟨u, t, hu, hb⟩ := nonMortalShortHoleBoundSelf _ _ _ _ (I.rename a b c d) hn
      exact ⟨u, t, (SelfTwoWordInstance.rename_isHole I a b c d u t).mp hu, Or.inl hb⟩
    · obtain ⟨u, t, hm⟩ := (SelfTwoWordInstance.rename_hasMortalHole I a b c d).mp hm
      obtain ⟨u', t', hm', hlen⟩ := Self.exists_short_mortalHole I hm
      exact ⟨u', t', hm'.1, Or.inr ⟨hm', hlen⟩⟩

end Instances

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-! ## Condition (I) -/

/-- **(I)-words** (`prop:as-bounds`(1)): (I) fails iff there are `p ∈ X^±` and a word `w` of
length less than `2^(2v+2s+2)` with `(p, w) ∈ μ_ψ` and `(p, w) ∉ μ_φ`. No satisfiability
hypothesis is needed. -/
theorem not_condI0_iff_short :
    ¬ CondI0 c φ ψ ↔ ∃ p : X × Bool, ∃ w : List (Fin n),
      w.length < 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 2) ∧
        (.inl p.1, p.2, w) ∈ Mu c ψ ∧ (p.1, p.2, w) ∉ Mu c φ := by
  rw [not_condI0_iff]
  constructor
  · rintro ⟨p, w, hw⟩
    obtain ⟨u, hu, hf⟩ := failureI0_short c φ ψ hw
    exact ⟨p, u, condI0Bound_eq X Z ▸ hu, (failureI0_iff c φ ψ p u).mp hf⟩
  · rintro ⟨p, w, -, hw⟩
    exact ⟨p, w, (failureI0_iff c φ ψ p w).mpr hw⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The (I) bound is at most `2^(4s+2)` (`prop:as-bounds`). -/
theorem condI0Bound_le :
    condI0Bound X Z ≤ 2 ^ (4 * (Fintype.card X + Fintype.card Z) + 2) := by
  rw [condI0Bound_eq]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-! ## Condition (U) -/

/-- **Condition (U) is decidable** (`thm:un-decidable`, first claim): for satisfiable `φ`,
(U) fails iff there are `p ∈ X^±` and a word `w` with `|w| ≤ holeBound(N_U, d_{N_U})` such
that `(p, w)` is live in `φ` and `DeadU_ψ(p, w)`. Here `holeBound(N_U, d_{N_U})` is
`holeLengthBound N_U` for the `N_U = |TargetState X Z|` states of the unit reader. -/
theorem not_condU_iff_short (hφ : ∃ ρ, SatT c ρ φ) :
    ¬ CondU c φ ψ ↔ ∃ p : X × Bool, ∃ w : List (Fin n),
      w.length ≤ holeLengthBound (Fintype.card (TargetState X Z)) ∧
        Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w := by
  classical
  rw [condU_iff_no_unit_holes c φ ψ hφ]
  push Not
  constructor
  · rintro ⟨p, w, hw⟩
    obtain ⟨w', hw', hlen⟩ := (hole_iff_bounded_length (unitReader c φ ψ p) unitRelation
      (unitTarget c φ ψ)).mp ⟨w, hw⟩
    obtain ⟨hu, hl⟩ := (unit_absHole_iff c φ ψ hφ p w').mp hw'
    exact ⟨p, w', hlen, hl, hu⟩
  · rintro ⟨p, w, -, hl, hu⟩
    exact ⟨p, w, (unit_absHole_iff c φ ψ hφ p w).mpr ⟨hu, hl⟩⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- **The closed form of (U)** (`thm:un-decidable`, last claim): if `X ≠ ∅`, then the unit
reader, with `N_U = 2^(4v+2h+1) = 2^(2v+2s+1)` states, satisfies
`holeBound(N_U, d_{N_U}) ≤ E₃(10v + 10s + 17) ≤ E₃(20s + 17)`. -/
theorem unitHoleBound_le (hX : 0 < Fintype.card X) :
    holeLengthBound (Fintype.card (TargetState X Z)) ≤
        E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ∧
      E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ≤
        E3 (20 * (Fintype.card X + Fintype.card Z) + 17) := by
  refine ⟨?_, E3_le_E3 (by omega)⟩
  rw [card_targetState_eq]
  exact (holeLengthBound_two_pow_le (by omega)).trans (E3_le_E3 (by omega))

/-- **(U)-words** (`prop:as-bounds`(2)): for satisfiable `φ`, if (U) fails, there is a
(U)-word of length at most `holeBound(N_U, d_{N_U}) ≤ E₃(10v + 10s + 17)`. -/
theorem exists_short_condU_word (hφ : ∃ ρ, SatT c ρ φ) (hU : ¬ CondU c φ ψ) :
    (∃ p : X × Bool, ∃ w : List (Fin n),
      w.length ≤ holeLengthBound (Fintype.card (TargetState X Z)) ∧
        Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w) ∧
      holeLengthBound (Fintype.card (TargetState X Z)) ≤
        E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) := by
  obtain ⟨p, w, h⟩ := (not_condU_iff_short c φ ψ hφ).mp hU
  exact ⟨⟨p, w, h⟩, (unitHoleBound_le (Fintype.card_pos_iff.mpr ⟨p.1⟩)).1⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The depth bound of the unit reader is below `2^(4v+4s+5)` (`sec:as-bounds`). -/
theorem unit_depth_lt :
    holeDepthBound (Fintype.card (TargetState X Z)) <
      2 ^ (4 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 5) := by
  unfold holeDepthBound
  rw [card_targetState_eq]
  have he : 2 ^ (4 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 5) =
      8 * (2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1)) ^ 2 := by
    ring
  have hN : 1 ≤ 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1) :=
    Nat.one_le_two_pow
  rw [he]
  generalize 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1) = N at hN ⊢
  have h2 : 2 * N * (4 * N - 1) ≤ 8 * N ^ 2 :=
    calc 2 * N * (4 * N - 1) ≤ 2 * N * (4 * N) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 8 * N ^ 2 := by ring
  have h3 : 1 ≤ 8 * N ^ 2 := by nlinarith
  omega

/-! ## Condition (II): the extracted instances -/

omit [DecidableEq X] [DecidableEq Z] in
/-- **Mortal bound for extracted instances** (`cor:mo-extracted`, first claim): for
`s = |X| + |Z| ≥ 1`, `Len♯_{I_pq} ≤ E₃(10v + 12s + 15) ≤ E₃(22s + 15)`, at every arity and
variance. `Len♯_{I_pq}` is `mortalHoleBound` at the state counts of `extractSelf`. -/
theorem extracted_mortalHoleBound_le (hs : 0 < Fintype.card X + Fintype.card Z) :
    extractedBoundSelf Mortal.mortalHoleBound X Z ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (22 * (Fintype.card X + Fintype.card Z) + 15) :=
  ⟨(extractedBoundSelf_eq X Z _).trans_le (mortalHoleBound_extracted_le hs),
    E3_le_E3 (by omega)⟩

/-- **Short mortal holes of extracted instances** (`cor:mo-extracted`, second claim): if
`I_pq` has a mortal hole, it has one whose separator word `u♯t` has length
`|u| + 1 + |t| ≤ E₃(22s + 15)`. -/
theorem exists_short_extracted_mortalHole (p q : X × Bool)
    (h : (extractSelf c φ ψ p q).HasMortalHole) :
    ∃ u t, (extractSelf c φ ψ p q).IsMortalHole u t ∧
      u.length + t.length + 1 ≤ E3 (22 * (Fintype.card X + Fintype.card Z) + 15) := by
  obtain ⟨u, t, hm⟩ := h
  obtain ⟨u', t', hm', hlen⟩ := Self.exists_short_mortalHole _ hm
  have hb := extracted_mortalHoleBound_le (X := X) (Z := Z)
    (by have := Fintype.card_pos_iff.mpr ⟨p.1⟩; omega)
  exact ⟨u', t', hm', hlen.trans (hb.1.trans hb.2)⟩

/-- **Hole words** (`prop:as-bounds`(3)): for satisfiable `φ`, if (U) holds and (II) fails,
there are `p, q ∈ X^±` and a hole `(u, t)` of `I_pq` such that either
`|u| + |t| ≤ Lnm(N_A, N_B, N_{A'}, N_{B'})`, or `(u, t)` is a mortal hole and
`|u♯t| = |u| + |t| + 1 ≤ Len♯_{I_pq} ≤ E₃(10v + 12s + 15)`. Condition (I) is not needed. -/
theorem exists_short_extracted_hole (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    (hII : ¬ CondII c φ ψ) :
    ∃ p q : X × Bool, ∃ u t : List (Fin n), (extractSelf c φ ψ p q).IsHole u t ∧
      (u.length + t.length ≤ extractedBoundSelf pumpHoleBound X Z ∨
        ((extractSelf c φ ψ p q).IsMortalHole u t ∧
          u.length + t.length + 1 ≤ extractedBoundSelf Mortal.mortalHoleBound X Z ∧
          extractedBoundSelf Mortal.mortalHoleBound X Z ≤
            E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15))) := by
  rw [condII_iff_no_holes hφ hU] at hII
  push Not at hII
  obtain ⟨p, q, hh⟩ := hII
  obtain ⟨u, t, ht, hb⟩ := exists_short_hole_or_mortalHole _ (extractSelf_forcedHeads p q) hh
  have hs : 0 < Fintype.card X + Fintype.card Z := by
    have := Fintype.card_pos_iff.mpr ⟨p.1⟩; omega
  refine ⟨p, q, u, t, ht, ?_⟩
  rcases hb with hb | ⟨hm, hb⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hm, hb, (extracted_mortalHoleBound_le hs).1⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The non-mortal bound of the extracted instances is a single exponential:
`Lnm(N_A, N_B, N_{A'}, N_{B'}) ≤ 54 N_A² N_B N_{A'} N_{B'} = 54 · 2^(6v+6s+1)`, so a
non-mortal hole word has length at most `Lnm + 1 < 2^(6v+6s+7)` (`prop:as-bounds`). -/
theorem extracted_pumpHoleBound_le :
    extractedBoundSelf pumpHoleBound X Z ≤
        54 * 2 ^ (6 * Fintype.card X + 6 * (Fintype.card X + Fintype.card Z) + 1) ∧
      extractedBoundSelf pumpHoleBound X Z + 1 <
        2 ^ (6 * Fintype.card X + 6 * (Fintype.card X + Fintype.card Z) + 7) := by
  rw [extractedBoundSelf_eq]
  exact ⟨pumpHoleBound_extracted_le, pumpHoleBound_extracted_lt⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The Π-reader of an extracted instance has `N_I ≤ 2^(2v+4s+2)` states, and the depth
bound `d_I = 2 N_I N_A - 1` of its mortal holes is below `2^(4v+4s+3)`, for `s ≥ 1`
(`cor:mo-extracted`, `sec:as-bounds`). -/
theorem extracted_piState_le (hs : 0 < Fintype.card X + Fintype.card Z) :
    Fintype.card (Mortal.State (SA := Finset (X × Bool)) (SB := TargetState X Z)
        (SA' := Finset ((X ⊕ Z) × Bool)) (SB' := Finset ((X ⊕ Z) × Bool))) ≤
        2 ^ (2 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 2) ∧
      2 * Fintype.card (Mortal.State (SA := Finset (X × Bool)) (SB := TargetState X Z)
          (SA' := Finset ((X ⊕ Z) × Bool)) (SB' := Finset ((X ⊕ Z) × Bool))) *
          Fintype.card (Finset (X × Bool)) - 1 <
        2 ^ (4 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 3) := by
  have hN := (card_extracted_piState X Z).trans_le (piStates_le hs)
  refine ⟨hN, ?_⟩
  rw [card_signedSet]
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN) (le_refl (2 ^ (2 * Fintype.card X)))
  have he : 2 * 2 ^ (2 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 2) *
      2 ^ (2 * Fintype.card X) =
      2 ^ (4 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 3) := by ring
  have hpos : 1 ≤ 2 ^ (4 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 3) :=
    Nat.one_le_two_pow
  omega

/-! ## Comparison of the bounds -/

omit [DecidableEq X] [DecidableEq Z] in
/-- **Comparison** (`prop:as-bounds`, last claims): if `v ≥ 1`, each bound of
`prop:as-bounds`(1)–(3) is at most `E₃(10v + 12s + 15) ≤ E₃(22s + 15)`: the (I) bound, the
(U) bound `holeBound(N_U, d_{N_U})`, the non-mortal hole-word bound `Lnm + 1`, and the mortal
bound `Len♯_{I_pq}`. Among the closed forms, the mortal one is the largest:
`E₃(10v + 10s + 17) ≤ E₃(10v + 12s + 15)`. -/
theorem counterexampleBounds_le (hX : 0 < Fintype.card X) :
    condI0Bound X Z ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      holeLengthBound (Fintype.card (TargetState X Z)) ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      extractedBoundSelf pumpHoleBound X Z + 1 ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      extractedBoundSelf Mortal.mortalHoleBound X Z ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ≤
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
      E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (22 * (Fintype.card X + Fintype.card Z) + 15) := by
  have hs : 0 < Fintype.card X + Fintype.card Z := by omega
  have hU := E3_le_E3 (show 10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17 ≤
    10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15 by omega)
  refine ⟨?_, (unitHoleBound_le hX).1.trans hU, ?_, (extracted_mortalHoleBound_le hs).1, hU,
    (extracted_mortalHoleBound_le hs).2⟩
  · rw [condI0Bound_eq]
    exact (Nat.pow_le_pow_right (by decide) (by omega)).trans (two_pow_le_E3 _)
  · exact (extracted_pumpHoleBound_le.2.le).trans
      ((Nat.pow_le_pow_right (by decide) (by omega)).trans (two_pow_le_E3 _))

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- **No visible variables** (`prop:as-bounds`, `v = 0`): if `X` is empty there is no
counterexample word, since (I), (U) and (II) hold. -/
theorem conditions_of_isEmpty [IsEmpty X] :
    CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ :=
  ⟨fun a _ => isEmptyElim a.1, fun a _ => isEmptyElim a.1, fun a _ => isEmptyElim a.1⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- Without visible variables, entailment between satisfiable systems holds. -/
theorem existsEntailsT_of_isEmpty [IsEmpty X] (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ :=
  (three_conditions_mixed hφ hψ).mpr (conditions_of_isEmpty c φ ψ)

/-! ## Short counterexamples -/

/-- **Short counterexamples over arbitrary trees** (the bound part of `thm:as-main`(3) for
`𝒟 = Trees`, via `prop:as-bounds`): if `φ` and `ψ` are satisfiable and `φ ⊭ ∃ Z. ψ`, then
`v ≥ 1`, and there is an (I)-word, a (U)-word, or, when (I) and (U) hold, a hole `(u, t)` of
an extracted instance, of length at most `E₃(10v + 12s + 15)`; for the hole the length is
that of the separator word, `|u| + |t| + 1`. -/
theorem exists_short_failure (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ)
    (h : ¬ ExistsEntailsT c φ ψ) :
    0 < Fintype.card X ∧
      ((∃ p : X × Bool, ∃ w : List (Fin n),
          w.length ≤ E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
            (.inl p.1, p.2, w) ∈ Mu c ψ ∧ (p.1, p.2, w) ∉ Mu c φ) ∨
        (∃ p : X × Bool, ∃ w : List (Fin n),
          w.length ≤ E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
            Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w) ∨
        (CondI0 c φ ψ ∧ CondU c φ ψ ∧ ∃ p q : X × Bool, ∃ u t : List (Fin n),
          (extractSelf c φ ψ p q).IsHole u t ∧ u.length + t.length + 1 ≤
            E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15))) := by
  have hX : 0 < Fintype.card X := by
    by_contra h0
    have : IsEmpty X := Fintype.card_eq_zero_iff.mp (by omega)
    exact h (existsEntailsT_of_isEmpty c φ ψ hφ hψ)
  obtain ⟨hI0, hUn, hpump, hmortal, -, -⟩ := counterexampleBounds_le (Z := Z) hX
  refine ⟨hX, ?_⟩
  rw [three_conditions_mixed hφ hψ] at h
  by_cases hi : CondI0 c φ ψ
  · by_cases hu : CondU c φ ψ
    · have hii : ¬ CondII c φ ψ := fun hii => h ⟨hi, hu, hii⟩
      obtain ⟨p, q, u, t, ht, hb⟩ := exists_short_extracted_hole c φ ψ hφ hu hii
      refine Or.inr (Or.inr ⟨hi, hu, p, q, u, t, ht, ?_⟩)
      rcases hb with hb | ⟨-, hb, -⟩
      · omega
      · exact hb.trans hmortal
    · obtain ⟨p, w, hw, hl, hd⟩ := (not_condU_iff_short c φ ψ hφ).mp hu
      exact Or.inr (Or.inl ⟨p, w, hw.trans hUn, hl, hd⟩)
  · obtain ⟨p, w, hw, hψw, hφw⟩ := (not_condI0_iff_short c φ ψ).mp hi
    refine Or.inl ⟨p, w, ?_, hψw, hφw⟩
    rw [← condI0Bound_eq] at hw
    exact hw.le.trans hI0

/-! ## The signature `{⊥, f}` -/

omit [DecidableEq X] [DecidableEq Z] in
/-- **The gadget doubles the variables** (`cor:tc-bf`): the gadget pair has the visible
variables `X ⊕ X` and the hidden variables `Z ⊕ Z`, so `v' = 2v` and `s' = 2s`. -/
theorem card_gadget_vars :
    Fintype.card (X ⊕ X) = 2 * Fintype.card X ∧
      Fintype.card (X ⊕ X) + Fintype.card (Z ⊕ Z) = 2 * (Fintype.card X + Fintype.card Z) := by
  simp only [Fintype.card_sum]
  omega

omit [DecidableEq X] [DecidableEq Z] in
/-- **The bound over `{⊥, f}`** (`cor:tc-bf`, `thm:as-main`(4)): at the gadget's variable
types, `E₃(10v' + 12s' + 15) = E₃(20v + 24s + 15) ≤ E₃(44s + 15)`. -/
theorem gadget_bound :
    E3 (10 * Fintype.card (X ⊕ X) + 12 * (Fintype.card (X ⊕ X) + Fintype.card (Z ⊕ Z)) + 15) =
        E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ∧
      E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (44 * (Fintype.card X + Fintype.card Z) + 15) := by
  obtain ⟨h1, h2⟩ := card_gadget_vars (X := X) (Z := Z)
  exact ⟨by rw [h2, h1]; ring_nf, E3_le_E3 (by omega)⟩

-- `DecidableEq (TargetState (X ⊕ X) (Z ⊕ Z))` exceeds the default instance size.
set_option synthInstance.maxSize 1024 in
/-- **Short counterexamples over `{⊥, f}`** (the bound part of `thm:as-main`(4) over
arbitrary trees): for covariant `f`, if the gadget pair `(φ♮, ψ♮)` of
`DeciENSSE.TopFree.existsEntailsT_iff_gadget` is satisfiable and its entailment fails, then
`v ≥ 1` and the gadget pair, over `X ⊕ X` and `Z ⊕ Z`, has an (I)-word, a (U)-word, or a
hole of an extracted instance, of length at most `E₃(20v + 24s + 15) ≤ E₃(44s + 15)`. -/
theorem exists_short_failure_gadget (xs : List X) (zs : List Z)
    (hφ : ∃ ρ, SatT (fun _ => false) ρ (TopFree.gadgetAnte xs φ))
    (hψ : ∃ ρ, SatT (fun _ => false) ρ (TopFree.gadgetCons zs ψ))
    (h : ¬ ExistsEntailsT (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ)) :
    0 < Fintype.card X ∧
      ((∃ p : (X ⊕ X) × Bool, ∃ w : List (Fin n),
          w.length ≤ E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ∧
            (.inl p.1, p.2, w) ∈ Mu (fun _ => false) (TopFree.gadgetCons zs ψ) ∧
            (p.1, p.2, w) ∉ Mu (fun _ => false) (TopFree.gadgetAnte xs φ)) ∨
        (∃ p : (X ⊕ X) × Bool, ∃ w : List (Fin n),
          w.length ≤ E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ∧
            Live (fun _ => false) (TopFree.gadgetAnte xs φ) (p.1, p.2, w) ∧
            DeadU (fun _ => false) (TopFree.gadgetCons zs ψ) p w) ∨
        (CondI0 (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ) ∧
          CondU (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ) ∧
          ∃ p q : (X ⊕ X) × Bool, ∃ u t : List (Fin n),
            (extractSelf (fun _ => false) (TopFree.gadgetAnte xs φ)
              (TopFree.gadgetCons zs ψ) p q).IsHole u t ∧
            u.length + t.length + 1 ≤
              E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15))) := by
  obtain ⟨hX, hc⟩ := exists_short_failure _ _ _ hφ hψ h
  rw [(gadget_bound (X := X) (Z := Z)).1] at hc
  rw [Fintype.card_sum] at hX
  exact ⟨by omega, hc⟩

end DeciENSSE.Bounds
