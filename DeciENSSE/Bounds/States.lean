import DeciENSSE.Core.Mixed.CondI0
import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Core.Words.Mortal.PiReader
import DeciENSSE.Bounds.Estimates

/-! # State counts of the readers of the decision procedure

For a visible variable set `X` and a hidden variable set `Z`, with `v = |X|`, `h = |Z|` and
`s = v + h`, every reader of the procedure has a state type built from signed summaries,
sets of signed variables. All states are counted, reachable or not:

- the membership readers of `μ` have `2^(2|V|+1)` states, and the product readers of the
  collision and (I0) searches have `2^(4|V|+2)` and `2^(2v+2s+2)` states (`lem:sm-mu`,
  `prop:sm-decide`);
- the unit reader of (U) and the target automaton `B` of the extracted instances have
  `N_U = N_B = 2^(4v+2h+1) = 2^(2v+2s+1)` states (`thm:un-decidable`, `sec:as-bounds`);
- the spine automaton has `N_A = 2^(2v)` states and both head automata have
  `N_{A'} = N_{B'} = 2^(2s)` states (`sec:as-bounds`);
- the Π-reader of an extracted instance has
  `N_I = 1 + 2^(2v+2s+1) + 2^(2v+4s+1)` states (`cor:mo-extracted`).

## Main declarations

- `card_signedSet`, `card_muState`, `muCollisionBound_eq`, `condI0Bound_eq`.
- `card_targetState`, `card_targetState_eq`: `N_U = N_B`.
- `extractedBoundSelf_eq`: the four state counts of the extracted instances.
- `card_extracted_piState`: `N_I` of the extracted instances.

The declarations are in the namespace `DeciENSSE.Bounds`.
-/

namespace DeciENSSE.Bounds
open DeciENSSE.Core.Mixed DeciENSSE.Core.Words

variable (V X Z : Type*) [Fintype V] [Fintype X] [Fintype Z]

/-- A set of signed variables over `V` is one of `2^(2|V|)` summaries. -/
theorem card_signedSet : Fintype.card (Finset (V × Bool)) = 2 ^ (2 * Fintype.card V) := by
  simp [Fintype.card_finset, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

/-- A membership reader of `μ` over `V` has `2^(2|V|+1)` states: a lower summary and a sticky
bit. -/
theorem card_muState : Fintype.card (MuState V) = 2 ^ (2 * Fintype.card V + 1) := by
  rw [Fintype.card_prod, card_signedSet, Fintype.card_bool, pow_succ]

/-- The collision search over `V` runs a product reader with `2^(4|V|+2)` states, the bound
of `prop:sm-decide`. -/
theorem muCollisionBound_eq : muCollisionBound V = 2 ^ (4 * Fintype.card V + 2) := by
  rw [muCollisionBound, Fintype.card_prod, card_muState, ← pow_add]
  ring_nf

/-- The (I0) search runs a product reader with `2^(2|X| + 2|X ∪ Z| + 2)` states, the bound
of `prop:sm-decide` and `prop:as-bounds`(1). -/
theorem condI0Bound_eq :
    condI0Bound X Z =
      2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 2) := by
  rw [condI0Bound, Fintype.card_prod, card_muState, card_muState, Fintype.card_sum, ← pow_add]
  ring_nf

/-- The unit reader and the target automaton share the state type `TargetState X Z`, with
`N_U = 2^(4|X| + 2|Z| + 1)` states (`thm:un-decidable`). -/
theorem card_targetState :
    Fintype.card (TargetState X Z) = 2 ^ (4 * Fintype.card X + 2 * Fintype.card Z + 1) := by
  change Fintype.card (Finset (X × Bool) × Bool × Finset ((X ⊕ Z) × Bool)) = _
  rw [Fintype.card_prod, Fintype.card_prod, card_signedSet, card_signedSet,
    Fintype.card_bool, Fintype.card_sum, ← pow_succ', ← pow_add]
  ring_nf

/-- `N_U = N_B = 2^(2v + 2s + 1)` with `v = |X|` and `s = |X| + |Z|` (`sec:as-bounds`). -/
theorem card_targetState_eq :
    Fintype.card (TargetState X Z) =
      2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1) := by
  rw [card_targetState]
  ring_nf

/-- The state counts of the extracted instances (`sec:as-bounds`): every bound `B` of the
procedure is evaluated at `N_A = 2^(2v)`, `N_B = 2^(2v+2s+1)` and `N_{A'} = N_{B'} = 2^(2s)`. -/
theorem extractedBoundSelf_eq (B : HoleBound) :
    extractedBoundSelf B X Z =
      B (2 ^ (2 * Fintype.card X))
        (2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1))
        (2 ^ (2 * (Fintype.card X + Fintype.card Z)))
        (2 ^ (2 * (Fintype.card X + Fintype.card Z))) := by
  rw [extractedBoundSelf, card_signedSet, card_targetState_eq, card_signedSet,
    Fintype.card_sum]

/-- The Π-reader of an extracted instance has `N_I = 1 + 2^(2v+2s+1) + 2^(2v+4s+1)` states,
reachable or not (`lem:mo-pi-reader`(i), `cor:mo-extracted`). -/
theorem card_extracted_piState :
    Fintype.card (Mortal.State (SA := Finset (X × Bool)) (SB := TargetState X Z)
        (SA' := Finset ((X ⊕ Z) × Bool)) (SB' := Finset ((X ⊕ Z) × Bool))) =
      1 + 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 1) +
        2 ^ (2 * Fintype.card X + 4 * (Fintype.card X + Fintype.card Z) + 1) := by
  rw [Mortal.card_state, card_signedSet, card_targetState_eq, card_signedSet,
    Fintype.card_sum, piStates_eq]

end DeciENSSE.Bounds
