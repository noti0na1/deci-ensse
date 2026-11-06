import DeciENSSE.Core.Mixed.CondI0

/-! # Roots, the pop bound and sign coherence of summaries

Facts about the signed pushdown summaries used in `lem:sm-roots`, `lem:sm-duality` and
`lem:sm-dead-states`: lower summaries are sign coherent like upper ones, the root of an
upper signed constructor literal is forbidden, a nonempty pop exposes a forbidden root,
root deadness alone gives the pop bound and passes to prefixes, and membership of a signed
variable in the root-dead and the support-dead region of the empty word is decidable.

## Main declarations

- `lower_sign_coherent`: sign coherence of lower summaries.
- `upper_signed_root_neg`, `pop_root_witness`: forbidden constructor roots.
- `root_cone`, `root_dead_prefix`: the pop bound from root deadness, and prefixes.
- `decideRootDeadEmpty`, `decideSupportDeadEmpty`: the two regions of the empty word.
-/
namespace DeciENSSE.Core.Mixed
open Full Words
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {χ : List (LitT n V)}

/-- Lower summaries have the same sign invariant as upper summaries. -/
theorem lower_sign_coherent {p r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Automata.Q (signedSys c χ) p w) :
    r.2 = Bool.xor p.2 (DeciNSSE.polarity c w) := by
  have he := Q_flip (c := c) (χ := χ) (flipV p) w
  simp only [flipV_flipV] at he
  rw [he, mem_map_flip] at h
  have hs := sign_coherent h
  simpa [flipV] using hs

omit [Fintype V] [DecidableEq V] in
/-- The root of an upper signed constructor literal is forbidden. -/
theorem upper_signed_root_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : Lit.lef r a ∈ signedSys c χ) : Neg χ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [signedMovesLit, Full.signedLit, moveLit, List.filterMap_cons,
    List.filterMap_nil, List.mem_cons, List.not_mem_nil,
    or_false, false_or, Lit.lef.injEq, reduceCtorEq] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fle hl
  · exact .lef hl

/-- A nonempty pop step exposes a forbidden constructor root and a pure path to it. -/
theorem pop_root_witness {p : V × Bool} {w : List (Fin n)} {i : Fin n}
    (h : (Automata.P (signedSys c χ) p (w ++ [i])).Nonempty) :
    ∃ r ∈ Automata.P (signedSys c χ) p w,
      (∃ a, Lit.lef r a ∈ signedSys c χ) ∧
      Moves c χ (p.1, p.2, w) (r.1, r.2, []) ∧ Neg χ (r.1, r.2, []) := by
  obtain ⟨b, hb⟩ := h
  rw [Automata.P_snoc, Automata.mem_pstep] at hb
  obtain ⟨r, hr, a, ha, _⟩ := hb
  exact ⟨r, hr, ⟨a, ha⟩, moves_iff_signed.mpr ((mem_P_iff_moves w).mp hr),
    upper_signed_root_neg ha⟩

/-- Root deadness alone suffices for the pop bound; support deadness is unnecessary. -/
theorem root_cone {p : V × Bool} {w : List (Fin n)} {k j : ℕ}
    (hk : ¬ ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, w.take k) a)
    (hkj : k < j) (hj : j ≤ w.length) :
    Automata.P (signedSys c χ) p (w.take j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hh := P_proper_prefix_neg ⟨r, hr⟩ (by simpa [List.length_take, Nat.min_eq_left hj] using hkj)
  have hd : ∃ z, (Automata.P (signedSys c χ) p (w.take k ++ z) ∩ NegDown c χ).Nonempty :=
    ⟨[], by simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkj)] using hh⟩
  exact hk (reach_neg_iff.mpr hd)

/-- Root deadness is inherited by word prefixes. -/
theorem root_dead_prefix {p : V × Bool} {u v : List (Fin n)}
    (h : ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, u ++ v) a) :
    ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, u) a := by
  obtain ⟨z, hz⟩ := reach_neg_iff.mp h
  exact reach_neg_iff.mpr ⟨v ++ z, by simpa [List.append_assoc] using hz⟩

/-- Executable membership in the empty-word root-dead region. -/
def decideRootDeadEmpty (c : Fin n → Bool) (χ : List (LitT n V)) (p : V × Bool) :
    Decidable (∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, []) a) := by
  apply decidable_of_iff (negReachS c χ (Automata.up (signedSys c χ) p))
  rw [reach_neg_iff, negReachS_iff]
  simp only [← Automata.P_nil, upperRun_P]

/-- Executable membership in the empty-word support-dead region. -/
def decideSupportDeadEmpty (c : Fin n → Bool) (χ : List (LitT n V)) (p : V × Bool) :
    Decidable (DeadT c χ p []) := by
  apply decidable_of_iff
    (negReachS c χ (Automata.up (signedSys c χ) p) ∨
      muReachS c χ (Automata.up (signedSys c χ) p) ∨
      flipHitS c χ (Automata.up (signedSys c χ) p))
  simpa only [List.length_nil, Nat.le_zero, exists_eq_left, List.take_zero, Automata.P_nil]
    using (deadT_iff_state (c := c) (χ := χ) (p := p) (u := [])).symm
end DeciENSSE.Core.Mixed
