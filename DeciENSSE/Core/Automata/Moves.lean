import DeciENSSE.Core.Automata.Powerset

/-! # Move paths, truncation, and common suffixes

Horn derivations combine stack moves with truncation of the last letter.
`truncation` postpones all truncations to the end. `lowest_point` then factors
a move path at a common suffix: the upper automaton consumes the source prefix,
and the lower automaton produces the target prefix.

The summary characterizations describe paths above a protected suffix:
`summaries_D` characterizes balanced paths, `summaries_P` prefix consumption,
and `summaries_Q` prefix production. Together these give the reachability step
needed to express covariant Horn closures as two-word comparisons.

## Main declarations

- `Automata.Moves`, `Automata.truncation`: move paths and postponed truncations.
- `Automata.summaries_D`, `Automata.summaries_P`, `Automata.summaries_Q`:
  saturation and automaton summaries as paths above a common suffix.
- `Automata.lowest_point`: the two-cut characterization of move reachability.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Move-only derivations; no facts and no truncations are included. -/
inductive Moves (χ : List (Lit n V)) (a : Config n V) : Config n V → Prop
  | refl : Moves χ a a
  | step {b c} : Moves χ a b → Move χ b c → Moves χ a c

namespace Moves
variable {χ : List (Lit n V)} {a b c : Config n V}
omit [Fintype V] [DecidableEq V] in
/-- Compose two move derivations. -/
theorem trans (h : Moves χ a b) (h' : Moves χ b c) : Moves χ a c := by
  induction h' with
  | refl => exact h
  | step _ hm ih => exact .step ih hm

omit [Fintype V] [DecidableEq V] in
/-- A move derivation is a Horn reachability derivation. -/
theorem reach (h : Moves χ a b) : Reach χ a b := by
  induction h with
  | refl => exact .refl
  | step _ hm ih => exact .step ih (.move hm)

omit [Fintype V] [DecidableEq V] in
/-- A move derivation preserves a common appended suffix. -/
theorem append (h : Moves χ a b) (σ : List (Fin n)) :
    Moves χ (a.1, a.2 ++ σ) (b.1, b.2 ++ σ) := by
  induction h with
  | refl => exact .refl
  | step _ hm ih =>
    apply Moves.step ih
    cases hm with
    | copy hl => exact .copy hl
    | push c hl => exact .push c hl
    | pop c hl => exact .pop c hl
end Moves

/-- A move derivation above σ, with σ deleted from every stack. Lifting such a derivation appends
σ back to every configuration. -/
def Above (χ : List (Lit n V)) (σ : List (Fin n)) (a b : Config n V) : Prop :=
  ∃ u v, a.2 = u ++ σ ∧ b.2 = v ++ σ ∧ Moves χ (a.1, u) (b.1, v)

omit [Fintype V] [DecidableEq V] in
/-- Remove the protected common suffix from an above-suffix derivation. -/
theorem above_iff {χ : List (Lit n V)} {a b : V} {u v σ : List (Fin n)} :
    Above χ σ (a, u ++ σ) (b, v ++ σ) ↔ Moves χ (a, u) (b, v) := by
  constructor
  · rintro ⟨u', v', hu, hv, h⟩
    have hu' : u = u' := List.append_cancel_right hu
    have hv' : v = v' := List.append_cancel_right hv
    simpa [hu', hv'] using h
  · intro h; exact ⟨u, v, rfl, rfl, h⟩

omit [Fintype V] [DecidableEq V] in
/-- A reachable stack can be truncated by any final suffix. -/
theorem reach_truncate {χ : List (Lit n V)} (y : V) (u v : List (Fin n)) :
    Reach χ (y, u ++ v) (y, u) := by
  induction v using List.reverseRecOn with
  | nil => simpa using (Reach.refl (χ := χ) (a := (y, u)))
  | append_singleton v c ih =>
    exact (Reach.step .refl (by
      simpa [List.append_assoc] using (Clause.trunc (χ := χ) y (u ++ v) c))).trans ih

omit [Fintype V] [DecidableEq V] in
/-- Replay the same moves while retaining each deleted suffix. -/
theorem truncation {χ : List (Lit n V)} {a b : Config n V} :
    Reach χ a b ↔ ∃ W, Moves χ a (b.1, W) ∧ b.2.IsPrefix W := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a.2, .refl, List.prefix_refl _⟩
    | @step b c _ hc ih =>
      obtain ⟨W, hm, v, hv⟩ := ih
      subst W
      cases hc with
      | trunc y w c =>
        exact ⟨(w ++ [c]) ++ v, hm, [c] ++ v, by simp [List.append_assoc]⟩
      | move h =>
        cases h with
        | copy hl => exact ⟨_ , .step hm (.copy hl), v, rfl⟩
        | push c hl => exact ⟨_ , .step hm (.push c hl), v, rfl⟩
        | pop c hl => exact ⟨_ , .step hm (.pop c hl), v, rfl⟩
  · rintro ⟨W, h, v, rfl⟩
    exact h.reach.trans (reach_truncate b.1 b.2 v)

/-- Balanced saturation consequences act at every unchanged suffix. -/
theorem d_moves {χ : List (Lit n V)} {a b : V} (h : (a, b) ∈ D χ) (w : List (Fin n)) :
    Moves χ (a, w) (b, w) := by
  have hh := mem_D_iff.mp h
  clear h
  induction hh generalizing w with
  | refl => exact .refl
  | copy h => exact .step .refl (.copy h)
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)
  | decomp c hl _ hu ih =>
    exact ((Moves.step .refl (.push c hl)).trans (ih (c :: w))).step (.pop c hu)

/-- Upper summaries give derivations that consume the read prefix. -/
theorem P_moves {χ : List (Lit n V)} {x b : V} {β : List (Fin n)}
    (h : b ∈ P χ x β) (σ : List (Fin n)) : Moves χ (x, β ++ σ) (b, σ) := by
  induction β using List.reverseRecOn generalizing b σ with
  | nil => exact d_moves (mem_up.mp h) σ
  | append_singleton β c ih =>
    rw [P_snoc, mem_pstep] at h
    obtain ⟨r, hr, bs, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((ih hr (c :: σ)).step (.pop c hl)).trans (d_moves hd σ)

/-- Lower summaries give derivations that produce the read prefix. -/
theorem Q_moves {χ : List (Lit n V)} {y a : V} {γ : List (Fin n)}
    (h : a ∈ Q χ y γ) (σ : List (Fin n)) : Moves χ (a, σ) (y, γ ++ σ) := by
  induction γ using List.reverseRecOn generalizing a σ with
  | nil => exact d_moves (mem_down.mp h) σ
  | append_singleton γ c ih =>
    rw [Q_snoc, mem_qstep] at h
    obtain ⟨r, hr, as, hl, hd⟩ := h
    simpa [List.append_assoc] using
      ((d_moves hd σ).step (.push c hl)).trans (ih hr (c :: σ))

/-- Changing the target along D preserves every lower summary. -/
theorem Q_target {χ : List (Lit n V)} {y z a : V} {w : List (Fin n)}
    (hyz : (y, z) ∈ D χ) (h : a ∈ Q χ y w) : a ∈ Q χ z w := by
  induction w using List.reverseRecOn generalizing a with
  | nil => exact mem_down.mpr (d_trans (mem_down.mp h) hyz)
  | append_singleton w c ih =>
    rw [Q_snoc, mem_qstep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- A push step preserves the lower-automaton summary. -/
theorem Q_push {χ : List (Lit n V)} {as : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hl : Lit.fle as y ∈ χ) (h : a ∈ Q χ (as c) w) :
    a ∈ Q χ y (c :: w) := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    exact mem_qstep.mpr ⟨y, mem_down.mpr (d_refl χ y), as, hl, mem_down.mp h⟩
  | append_singleton w d ih =>
    rw [Q_snoc, mem_qstep] at h
    change a ∈ Q χ y ((c :: w) ++ [d])
    rw [Q_snoc, mem_qstep]
    obtain ⟨r, hr, bs, hb, hd⟩ := h
    exact ⟨r, ih hr, bs, hb, hd⟩

/-- A pop step preserves the lower-automaton summary. -/
theorem Q_pop {χ : List (Lit n V)} {bs : Fin n → V} {y a : V} {w : List (Fin n)} (c : Fin n)
    (hu : Lit.lef y bs ∈ χ) (h : a ∈ Q χ y (c :: w)) :
    a ∈ Q χ (bs c) w := by
  induction w using List.reverseRecOn generalizing a with
  | nil =>
    obtain ⟨r, hr, as, hl, hd⟩ := mem_qstep.mp h
    exact mem_down.mpr (d_trans hd (d_decomp c hl (mem_down.mp hr) hu))
  | append_singleton w d ih =>
    change a ∈ Q χ y ((c :: w) ++ [d]) at h
    rw [Q_snoc, mem_qstep] at h ⊢
    obtain ⟨r, hr, as, hl, hd⟩ := h
    exact ⟨r, ih hr, as, hl, hd⟩

/-- The common-suffix form of a lowest-point decomposition. -/
def Normal (χ : List (Lit n V)) (x : V) (u : List (Fin n)) (y : V) (t : List (Fin n)) : Prop :=
  ∃ β γ σ v, u = β ++ σ ∧ t = γ ++ σ ∧ v ∈ P χ x β ∧ v ∈ Q χ y γ

/-- One move preserves the normal-form summary. -/
theorem normal_step {χ : List (Lit n V)} {x y z : V} {u t w : List (Fin n)}
    (h : Normal χ x u y t) (hm : Move χ (y, t) (z, w)) : Normal χ x u z w := by
  obtain ⟨β, γ, σ, v, hu, ht, hp, hq⟩ := h
  cases hm with
  | copy hl => exact ⟨β, γ, σ, v, hu, ht, hp, Q_target (d_copy hl) hq⟩
  | push c hl =>
    exact ⟨β, c :: γ, σ, v, hu, congrArg (List.cons c) ht, hp, Q_push c hl hq⟩
  | @pop r as w c hl =>
    cases γ with
    | nil =>
      have hs : σ = c :: w := ht.symm
      refine ⟨β ++ [c], [], w, (as c), ?_, rfl, ?_, ?_⟩
      · simpa [hs, List.append_assoc] using hu
      · rw [P_snoc, mem_pstep]
        exact ⟨y, P_closed hp (mem_down.mp hq), as, hl, d_refl χ _⟩
      · exact mem_down.mpr (d_refl χ _)
    | cons d γ =>
      have he := List.cons.inj ht
      obtain ⟨rfl, hw⟩ := he
      exact ⟨β, γ, σ, v, hu, hw, hp, Q_pop c hl hq⟩

/-- Every move path has a lowest-point decomposition, proved by preserving its normal form under
copies, pushes, and pops. -/
theorem moves_normal {χ : List (Lit n V)} {a b : Config n V} (h : Moves χ a b) :
    Normal χ a.1 a.2 b.1 b.2 := by
  induction h with
  | refl => exact ⟨[], [], a.2, a.1, rfl, rfl,
      mem_up.mpr (d_refl χ _), mem_down.mpr (d_refl χ _)⟩
  | step _ hm ih => exact normal_step ih hm

/-- A normal-form summary supplies a move derivation. -/
theorem normal_moves {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal χ x u y t) : Moves χ (x, u) (y, t) := by
  obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := h
  exact (P_moves hp σ).trans (Q_moves hq σ)

/-- Saturation summarizes derivations above a protected common suffix. -/
theorem summaries_D {χ : List (Lit n V)} {a b : V} (w : List (Fin n)) :
    (a, b) ∈ D χ ↔ Above χ w (a, w) (b, w) := by
  change (a, b) ∈ D χ ↔ Above χ w (a, [] ++ w) (b, [] ++ w)
  rw [above_iff]
  constructor
  · intro h; exact d_moves h []
  · intro h
    obtain ⟨β, γ, σ, v, hβ, hγ, hp, hq⟩ := moves_normal h
    have hb : β = [] ∧ σ = [] := List.append_eq_nil_iff.mp hβ.symm
    have hg : γ = [] := (List.append_eq_nil_iff.mp hγ.symm).1
    simp only [hb.1, hg, P_nil, Q_nil, mem_up, mem_down] at hp hq
    exact d_trans hp hq

/-- Upper summaries characterize prefix-consuming derivations. -/
theorem summaries_P {χ : List (Lit n V)} {x b : V} (β σ : List (Fin n)) :
    b ∈ P χ x β ↔ Above χ σ (x, β ++ σ) (b, σ) := by
  change b ∈ P χ x β ↔ Above χ σ (x, β ++ σ) (b, [] ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using P_moves h []
  · intro h
    obtain ⟨β', γ, σ', v, he, hz, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst β'
    exact P_closed hp (mem_down.mp hq)

/-- Lower summaries characterize prefix-producing derivations. -/
theorem summaries_Q {χ : List (Lit n V)} {y a : V} (γ σ : List (Fin n)) :
    a ∈ Q χ y γ ↔ Above χ σ (a, σ) (y, γ ++ σ) := by
  change a ∈ Q χ y γ ↔ Above χ σ (a, [] ++ σ) (y, γ ++ σ)
  rw [above_iff]
  constructor
  · intro h; simpa using Q_moves h []
  · intro h
    obtain ⟨β, γ', σ', v, hz, he, hp, hq⟩ := moves_normal h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hz.symm
    simp only [List.append_nil] at he
    subst γ'
    exact Q_closed hq (mem_up.mp hp)

/-- Factor a move derivation at its lowest stack height, with two bounded cuts. -/
theorem lowest_point {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    Moves χ (x, u) (y, t) ↔ ∃ s ≤ u.length, ∃ e ≤ t.length,
      u.drop s = t.drop e ∧
      (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty := by
  constructor
  · intro h
    obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := moves_normal h
    refine ⟨β.length, by simp, γ.length, by simp, ?_, ?_⟩
    · simp
    · simpa using (show (P χ x β ∩ Q χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
  · rintro ⟨s, _, e, _, he, v, hv⟩
    apply normal_moves
    exact ⟨u.take s, t.take e, u.drop s, v, (List.take_append_drop s u).symm,
      he ▸ (List.take_append_drop e t).symm, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

end Automata
end DeciENSSE.Core
