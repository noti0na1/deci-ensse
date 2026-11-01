import DeciENSSE.Core.Horn
import Mathlib.Data.Fintype.Prod

/-! # Saturating covariant variable inequalities

The finite relation `D` closes variable inequalities under reflexivity,
transitivity, and decomposition of matching constructor bounds. `mem_D_iff`
proves that the executable saturation produces exactly the pairs derivable by
these rules. The upper and lower automata use this relation between stack moves.

This is the finite-summary step of the covariant automata construction. Its
namespace is `DeciENSSE.Core.Automata`, shared by the following automata modules.

## Main declarations

- `Automata.round`, `Automata.saturate`, `Automata.D`: finite saturation.
- `Automata.Deriv`, `Automata.mem_D_iff`: the derivation characterization.
-/

namespace DeciENSSE.Core
namespace Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Accessor searches enumerate literals, not the function space of children. -/
theorem exists_fleArgs_iff (χ : List (Lit n V))
    (F : ((Fin n → V) × V) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.fleArgs?, F p) ↔
      ∃ a u, Lit.fle a u ∈ χ ∧ F (a, u) := by
  constructor
  · rintro ⟨l, hl, ⟨a, u⟩, hp, h⟩
    have he := (Lit.mem_fleArgs? l a u).mp hp
    subst l
    exact ⟨a, u, hl, h⟩
  · rintro ⟨a, u, hl, h⟩
    exact ⟨.fle a u, hl, (a, u), (Lit.mem_fleArgs? _ _ _).mpr rfl, h⟩

omit [Fintype V] [DecidableEq V] in
/-- Accessor searches recognize constructor upper bounds in a literal list. -/
theorem exists_lefArgs_iff (χ : List (Lit n V))
    (F : (V × (Fin n → V)) → Prop) :
    (∃ l ∈ χ, ∃ p ∈ l.lefArgs?, F p) ↔
      ∃ u a, Lit.lef u a ∈ χ ∧ F (u, a) := by
  constructor
  · rintro ⟨l, hl, ⟨u, a⟩, hp, h⟩
    have he := (Lit.mem_lefArgs? l u a).mp hp
    subst l
    exact ⟨u, a, hl, h⟩
  · rintro ⟨u, a, hl, h⟩
    exact ⟨.lef u a, hl, (u, a), (Lit.mem_lefArgs? _ _ _).mpr rfl, h⟩

/-- One simultaneous round of the four rules; decomposition visits every child. -/
def round (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  R ∪ Finset.univ.filter fun p => p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
    (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
    ∃ l ∈ χ, ∃ a ∈ l.fleArgs?, ∃ k ∈ χ, ∃ b ∈ k.lefArgs?,
      ∃ i : Fin n, (a.2, b.1) ∈ R ∧ p.1 = a.1 i ∧ p.2 = b.2 i

/-- Membership in one saturation round expands into the four deduction rules. -/
@[simp] theorem mem_round {χ : List (Lit n V)} {R : Finset (V × V)} {p : V × V} :
    p ∈ round χ R ↔ p ∈ R ∨ p.1 = p.2 ∨ Lit.le p.1 p.2 ∈ χ ∨
      (∃ v, (p.1, v) ∈ R ∧ (v, p.2) ∈ R) ∨
      ∃ a b u v, ∃ i : Fin n, Lit.fle a u ∈ χ ∧ (u, v) ∈ R ∧
        Lit.lef v b ∈ χ ∧ p.1 = a i ∧ p.2 = b i := by
  simp only [round, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_fleArgs_iff, exists_lefArgs_iff]
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  apply or_congr_right
  constructor
  · rintro ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩
    exact ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
  · rintro ⟨a, b, u, v, i, hl, hd, hu, hx, hy⟩
    exact ⟨a, u, hl, v, b, hu, i, hd, hx, hy⟩

/-- Each saturation round retains all existing pairs. -/
theorem subset_round (χ : List (Lit n V)) (R : Finset (V × V)) : R ⊆ round χ R :=
  Finset.subset_union_left

/-- Saturation terminates because every recursive round adds a pair. -/
def saturate (χ : List (Lit n V)) (R : Finset (V × V)) : Finset (V × V) :=
  if _h : round χ R ⊆ R then R else saturate χ (round χ R)
termination_by Fintype.card (V × V) - R.card
decreasing_by
  have hlt : R.card < (round χ R).card :=
    Finset.card_lt_card (ssubset_iff_subset_not_subset.mpr ⟨subset_round χ R, _h⟩)
  have hle := Finset.card_le_univ (round χ R)
  omega

/-- The finite saturated relation on variables. -/
def D (χ : List (Lit n V)) : Finset (V × V) := saturate χ ∅

/-- The saturated relation is closed under one round. -/
theorem saturate_closed (χ : List (Lit n V)) (R : Finset (V × V)) :
    round χ (saturate χ R) ⊆ saturate χ R := by
  fun_induction saturate χ R with
  | case1 R h => exact h
  | case2 R h ih => exact ih

/-- The inductive presentation used to reason about the executable saturation. -/
inductive Deriv (χ : List (Lit n V)) : V → V → Prop
  | refl (x) : Deriv χ x x
  | copy {x y} : Lit.le x y ∈ χ → Deriv χ x y
  | trans {x y z} : Deriv χ x y → Deriv χ y z → Deriv χ x z
  | decomp {as bs : Fin n → V} {u v} (c : Fin n) : Lit.fle as u ∈ χ →
      Deriv χ u v → Lit.lef v bs ∈ χ →
      Deriv χ (as c) (bs c)

/-- One round preserves derivability of variable inequalities. -/
theorem round_sound {χ : List (Lit n V)} {R : Finset (V × V)}
    (hR : ∀ p ∈ R, Deriv χ p.1 p.2) : ∀ p ∈ round χ R, Deriv χ p.1 p.2 := by
  intro p hp
  rcases mem_round.mp hp with hp | hp
  · exact hR p hp
  · rcases hp with h | h | ⟨v, h₁, h₂⟩ |
      ⟨as, bs, u, v, c, hl, hd, hu, h₁, h₂⟩
    · rw [h]; exact .refl _
    · exact .copy h
    · exact .trans (hR (p.1, v) h₁) (hR (v, p.2) h₂)
    · rw [h₁, h₂]; exact .decomp c hl (hR _ hd) hu

/-- Every pair produced by saturation has an inductive derivation. -/
theorem saturate_sound (χ : List (Lit n V)) (R : Finset (V × V))
    (hR : ∀ p ∈ R, Deriv χ p.1 p.2) :
    ∀ p ∈ saturate χ R, Deriv χ p.1 p.2 := by
  fun_induction saturate χ R with
  | case1 => exact hR
  | case2 R _ ih => exact ih (round_sound hR)

/-- The saturated relation is characterized by its closure rules. -/
theorem mem_D_iff {χ : List (Lit n V)} {x y : V} : (x, y) ∈ D χ ↔ Deriv χ x y := by
  constructor
  · exact saturate_sound χ ∅ (by simp) (x, y)
  · intro h
    have hc := saturate_closed χ ∅
    induction h with
    | refl x => exact hc (by simp)
    | copy h => exact hc (by simp [h])
    | trans _ _ ih₁ ih₂ =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, ih₁, ih₂⟩)))
    | decomp c hl _ hu ih =>
      apply hc; apply mem_round.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, c, hl, ih, hu, rfl, rfl⟩)))

/-- The saturated relation is reflexive. -/
theorem d_refl (χ : List (Lit n V)) (x : V) : (x, x) ∈ D χ := mem_D_iff.mpr (.refl x)
/-- A variable inequality is present in the saturated relation. -/
theorem d_copy {χ : List (Lit n V)} {x y : V} (h : Lit.le x y ∈ χ) :
    (x, y) ∈ D χ := mem_D_iff.mpr (.copy h)
/-- The saturated relation is transitive. -/
theorem d_trans {χ : List (Lit n V)} {x y z : V}
    (h : (x, y) ∈ D χ) (h' : (y, z) ∈ D χ) : (x, z) ∈ D χ :=
  mem_D_iff.mpr (.trans (mem_D_iff.mp h) (mem_D_iff.mp h'))
/-- Matching constructor bounds imply inequalities between corresponding children. -/
theorem d_decomp {χ : List (Lit n V)} {as bs : Fin n → V} {u v : V} (c : Fin n)
    (hl : Lit.fle as u ∈ χ) (hd : (u, v) ∈ D χ) (hu : Lit.lef v bs ∈ χ) :
    ((as c), (bs c)) ∈ D χ :=
  mem_D_iff.mpr (.decomp c hl (mem_D_iff.mp hd) hu)

end Automata
end DeciENSSE.Core
