import DeciENSSE.Core.Full.Signed
import DeciENSSE.Core.Mixed.LeafHorn
import DeciENSSE.Core.Automata.Moves

/-! # Covariant automata for signed leaf moves

The full signed translation duplicates variables and switches signs at
contravariant children, as in `DeciNSSE.signed`. Dropping its extreme-label
units leaves copy, push, and pop moves for finite pushdown systems. The units
remain separate seeds and exclusions in the leaf Horn presentation.

## Main declarations

- `signedSys`, `move_iff_signed`, `moves_iff_signed`,
  `D_dual`, `Q_flip`, `mem_P_iff_moves`, `popRoot`, `P_nil_absorb`,
  `lowest_point_leaf`, `sign_coherent`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words
open DeciNSSE DeciENSSE.Core.Full
variable {n : ℕ} {V : Type*}

/-- Forget extreme-label units when extracting the leaf automaton's moves. -/
def moveLit : LitT n V → Option (Lit n V)
  | .le u v => some (.le u v)
  | .fle a u => some (.fle a u)
  | .lef u a => some (.lef u a)
  | .bot _ | .top _ => none

/-- The full signed translation with extreme-label units omitted.
Those units are handled separately by the positive and negative seed sets. -/
def signedMovesLit (c : Fin n → Bool) (l : LitT n V) : List (Lit n (V × Bool)) :=
  (Full.signedLit c l).filterMap moveLit

/-- Translate all mixed literals into a signed covariant system. -/
def signedSys (c : Fin n → Bool) (χ : List (LitT n V)) : List (Lit n (V × Bool)) :=
  χ.flatMap (signedMovesLit c)

/-- Reassociate mixed configurations as signed-variable configurations. -/
def assoc : Config n V ≃ DeciENSSE.Core.Config n (V × Bool) where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, p.1.2, p.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {c : Fin n → Bool} {χ : List (LitT n V)}

private theorem signed_mem {l : LitT n V} {k : Lit n (V × Bool)}
    (hl : l ∈ χ) (hk : k ∈ signedMovesLit c l) : k ∈ signedSys c χ :=
  List.mem_flatMap.mpr ⟨l, hl, hk⟩

private theorem move_to_signed {p q : Config n V} (h : Move c χ p q) :
    DeciENSSE.Core.Move (signedSys c χ) (assoc p) (assoc q) := by
  cases h with
  | copyPlus hl => exact .copy (signed_mem hl (by simp [signedMovesLit, Full.signedLit, moveLit]))
  | copyMinus hl => exact .copy (signed_mem hl (by simp [signedMovesLit, Full.signedLit, moveLit]))
  | @flePush a u w i hl =>
    exact DeciENSSE.Core.Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fle (fun j => (a j, c j)) (u, false) ∈
        signedMovesLit c (.fle a u) by simp [signedMovesLit, Full.signedLit, moveLit]))
  | @flePop a u w i hl =>
    exact DeciENSSE.Core.Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.lef (u, true) (fun j => (a j, !(c j))) ∈
        signedMovesLit c (.fle a u) by simp [signedMovesLit, Full.signedLit, moveLit]))
  | @lefPop u a w i hl =>
    exact DeciENSSE.Core.Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.lef (u, false) (fun j => (a j, c j)) ∈
        signedMovesLit c (.lef u a) by simp [signedMovesLit, Full.signedLit, moveLit]))
  | @lefPush u a w i hl =>
    exact DeciENSSE.Core.Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fle (fun j => (a j, !(c j))) (u, true) ∈
        signedMovesLit c (.lef u a) by simp [signedMovesLit, Full.signedLit, moveLit]))

private theorem signed_to_move {p q : DeciENSSE.Core.Config n (V × Bool)}
    (h : DeciENSSE.Core.Move (signedSys c χ) p q) :
    Move c χ (assoc.symm p) (assoc.symm q) := by
  cases h with
  | copy hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMovesLit, Full.signedLit, moveLit, List.filterMap_cons,
      List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, Lit.le.injEq, reduceCtorEq] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .copyPlus hsrc
    · exact .copyMinus hsrc
  | push i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMovesLit, Full.signedLit, moveLit, List.filterMap_cons,
      List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, false_or, Lit.fle.injEq, reduceCtorEq] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .flePush (c := c) i hsrc
    · exact .lefPush (c := c) i hsrc
  | pop i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedMovesLit, Full.signedLit, moveLit, List.filterMap_cons,
      List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, false_or, Lit.lef.injEq, reduceCtorEq] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .flePop _ hsrc
    · exact .lefPop _ hsrc

/-- The signed translation preserves and reflects single moves. -/
theorem move_iff_signed {p q : Config n V} : Move c χ p q ↔
    DeciENSSE.Core.Move (signedSys c χ) (assoc p) (assoc q) :=
  ⟨move_to_signed, signed_to_move⟩

/-- The signed translation preserves and reflects pure paths. -/
theorem moves_iff_signed {p q : Config n V} :
    Relation.ReflTransGen (Move c χ) p q ↔
      Automata.Moves (signedSys c χ) (assoc p) (assoc q) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hm ih => exact .step ih (move_to_signed hm)
  · intro h
    have lift {a b} (hh : Automata.Moves (signedSys c χ) a b) :
        Relation.ReflTransGen (Move c χ) (assoc.symm a) (assoc.symm b) := by
      induction hh with
      | refl => exact .refl
      | step _ hm ih => exact .tail ih (signed_to_move hm)
    exact lift h

/-- Flip the sign of a signed variable. -/
def flipV (p : V × Bool) : V × Bool := (p.1, !p.2)

/-- Flipping a signed variable twice is the identity. -/
@[simp] theorem flipV_flipV (p : V × Bool) : flipV (flipV p) = p := by
  simp [flipV]

/-- The sign flip as a finite-set embedding. -/
def flipEmb : (V × Bool) ↪ (V × Bool) :=
  ⟨flipV, fun _ _ h => by simpa using congrArg flipV h⟩

/-- The sign-flip embedding acts by Boolean negation. -/
@[simp] theorem flipEmb_apply (p : V × Bool) : flipEmb p = flipV p := rfl

/-- Reverse a rule and flip the signs of its variables. -/
def dualLit : Lit n (V × Bool) → Lit n (V × Bool)
  | .le x y => .le (flipV y) (flipV x)
  | .fle a u => .lef (flipV u) (fun i => flipV (a i))
  | .lef u a => .fle (fun i => flipV (a i)) (flipV u)

/-- Signed paths reverse under sign flip. -/
theorem signed_dual {l : Lit n (V × Bool)} (h : l ∈ signedSys c χ) :
    dualLit l ∈ signedSys c χ := by
  obtain ⟨k, hk, hl⟩ := List.mem_flatMap.mp h
  apply signed_mem hk
  cases k <;> simp [signedMovesLit, Full.signedLit, moveLit] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualLit, flipV]

/-- Word concatenation composes parity changes. -/
theorem polarity_append (c : Fin n → Bool) (u v : List (Fin n)) :
    DeciNSSE.polarity c (u ++ v) = Bool.xor (DeciNSSE.polarity c u) (DeciNSSE.polarity c v) := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih]

/-- Every pure move preserves sign xor remaining-word parity. -/
theorem move_sign {p q : Config n V} (h : Move c χ p q) :
    Bool.xor q.2.1 (DeciNSSE.polarity c q.2.2) =
      Bool.xor p.2.1 (DeciNSSE.polarity c p.2.2) := by
  cases h <;> simp

/-- A pure path preserves the variance-adjusted sign. -/
theorem moves_sign {p q : Config n V}
    (h : Relation.ReflTransGen (Move c χ) p q) :
    Bool.xor q.2.1 (DeciNSSE.polarity c q.2.2) =
      Bool.xor p.2.1 (DeciNSSE.polarity c p.2.2) := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact (move_sign hm).trans ih

section Automata
variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem deriv_dual {x y : V × Bool}
    (h : Automata.Deriv (signedSys c χ) x y) :
    Automata.Deriv (signedSys c χ) (flipV y) (flipV x) := by
  induction h with
  | refl => exact .refl _
  | copy hl => exact .copy (signed_dual hl)
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
  | decomp i hl _ hu ih =>
    exact Automata.Deriv.decomp i (signed_dual hu) ih (signed_dual hl)

/-- Sign flip reverses the saturated summary relation. -/
theorem D_dual {x y : V × Bool} :
    (x, y) ∈ Automata.D (signedSys c χ) ↔
      (flipV y, flipV x) ∈ Automata.D (signedSys c χ) := by
  constructor
  · exact fun h => Automata.mem_D_iff.mpr (deriv_dual (Automata.mem_D_iff.mp h))
  · intro h
    simpa using Automata.mem_D_iff.mpr (deriv_dual (Automata.mem_D_iff.mp h))

omit [Fintype V] [DecidableEq V] in
/-- Membership in a flipped finite set is opposite-sign membership. -/
@[simp] theorem mem_map_flip {S : Finset (V × Bool)} {x : V × Bool} :
    x ∈ S.map flipEmb ↔ flipV x ∈ S := by
  simp only [Finset.mem_map, flipEmb_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨flipV x, h, flipV_flipV x⟩

/-- Lower summaries are flipped upper summaries. -/
theorem down_flip (y : V × Bool) :
    Automata.down (signedSys c χ) (flipV y) =
      (Automata.up (signedSys c χ) y).map flipEmb := by
  ext x
  simp only [Automata.mem_down, mem_map_flip, Automata.mem_up]
  simpa using (D_dual (x := x) (y := flipV y))

/-- A lower-reader step is a flipped upper-reader step. -/
theorem qstep_flip (S : Finset (V × Bool)) (i : Fin n) :
    Automata.qstep (signedSys c χ) (S.map flipEmb) i =
      (Automata.pstep (signedSys c χ) S i).map flipEmb := by
  ext x
  simp only [Automata.mem_qstep, mem_map_flip, Automata.mem_pstep]
  constructor
  · rintro ⟨r, hr, a, hl, hd⟩
    refine ⟨flipV r, hr, (fun j => flipV (a j)), signed_dual hl, ?_⟩
    exact D_dual.mp hd
  · rintro ⟨r, hr, a, hl, hd⟩
    refine ⟨flipV r, by simpa using hr, (fun j => flipV (a j)), signed_dual hl, ?_⟩
    have hh := D_dual.mp hd
    simpa using hh

/-- Lower-reader runs are flipped upper-reader runs. -/
theorem Q_flip (y : V × Bool) (w : List (Fin n)) :
    Automata.Q (signedSys c χ) (flipV y) w =
      (Automata.P (signedSys c χ) y w).map flipEmb := by
  induction w using List.reverseRecOn with
  | nil => exact down_flip y
  | append_singleton w i ih => rw [Automata.Q_snoc, Automata.P_snoc, ih, qstep_flip]

/-- Upper summaries characterize paths to the empty word. -/
theorem mem_P_iff_moves {x r : V × Bool} (β : List (Fin n)) :
    r ∈ Automata.P (signedSys c χ) x β ↔
      Automata.Moves (signedSys c χ) (x, β) (r, []) := by
  have h := Automata.summaries_P (χ := signedSys c χ) (x := x) (b := r) β []
  simpa only [List.append_nil] using h.trans
    (Automata.above_iff (u := β) (v := []) (σ := []))

omit [Fintype V] [DecidableEq V] in
private theorem signed_lef_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : Lit.lef r a ∈ signedSys c χ) : Neg χ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [signedMovesLit, Full.signedLit, moveLit, List.filterMap_cons,
    List.filterMap_nil, List.mem_cons, List.not_mem_nil,
    or_false, false_or, Lit.lef.injEq, reduceCtorEq] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fle hl
  · exact .lef hl

/-- Root variables obtainable by popping a signed word. -/
theorem popRoot {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Automata.P (signedSys c χ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Automata.P (signedSys c χ) x β, Neg χ (r.1, r.2, []) := by
  obtain ⟨a, ha⟩ := h
  rw [Automata.P_snoc, Automata.mem_pstep] at ha
  obtain ⟨r, hr, a, hl, _⟩ := ha
  exact ⟨r, hr, signed_lef_neg hl⟩

/-- The empty-word upper summary absorbs further summary closure. -/
theorem P_nil_absorb {x : V × Bool} {β : List (Fin n)}
    (h : Automata.P (signedSys c χ) x β = ∅) (γ : List (Fin n)) :
    Automata.P (signedSys c χ) x (β ++ γ) = ∅ := by
  induction γ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w i ih => rw [← List.append_assoc, Automata.P_snoc, ih, Automata.pstep_empty]

/-- A pure path factors through its lowest word position. -/
theorem lowest_point_leaf {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c χ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.P (signedSys c χ) (p, s) (u.take i) ∩
          Automata.Q (signedSys c χ) (q, s') (t.take e)).Nonempty := by
  rw [moves_iff_signed]
  exact Automata.lowest_point

/-- All variables in one upper state have the same sign. -/
theorem sign_coherent {p : V} {s : Bool} {r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Automata.P (signedSys c χ) (p, s) w) :
    r.2 = Bool.xor s (DeciNSSE.polarity c w) := by
  have hm := (mem_P_iff_moves w).mp h
  have hh : Relation.ReflTransGen (Move c χ) (p, s, w) (r.1, r.2, []) :=
    moves_iff_signed.mpr hm
  simpa using moves_sign hh

end Automata

end DeciENSSE.Core.Mixed
