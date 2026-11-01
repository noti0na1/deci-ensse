import DeciENSSE.Core.Mixed.LeafHorn
import DeciENSSE.Core.Automata

/-! # Covariant automata for signed leaf moves

Signed variables translate mixed leaf moves into finite pushdown systems.
The resulting automata describe pure paths over the child alphabet.

## Main declarations

- `signedSys`, `move_iff_signed`, `moves_iff_signed`,
  `D_dual`, `Q_flip`, `mem_P_iff_moves`, `popRoot`, `P_nil_absorb`,
  `lowest_point_leaf`, `sign_coherent`.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full
variable {n : ℕ} {V : Type*}

/-- Translate a mixed literal into its two signed covariant implications. -/
def signedLit (c : Fin n → Bool) : LitT n V → List (Lit n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .fle a u => [.fle (fun i => (a i, c i)) (u, false),
      .lef (u, true) (fun i => (a i, !(c i)))]
  | .lef u a => [.lef (u, false) (fun i => (a i, c i)),
      .fle (fun i => (a i, !(c i))) (u, true)]
  | .bot _ | .top _ => []

/-- Translate all mixed literals into a signed covariant system. -/
def signedSys (c : Fin n → Bool) (χ : List (LitT n V)) : List (Lit n (V × Bool)) :=
  χ.flatMap (signedLit c)

/-- Reassociate mixed configurations as signed-variable configurations. -/
def assoc : Config n V ≃ DeciENSSE.Core.Config n (V × Bool) where
  toFun p := ((p.1, p.2.1), p.2.2)
  invFun p := (p.1.1, p.1.2, p.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {c : Fin n → Bool} {χ : List (LitT n V)}

private theorem signed_mem {l : LitT n V} {k : Lit n (V × Bool)}
    (hl : l ∈ χ) (hk : k ∈ signedLit c l) : k ∈ signedSys c χ :=
  List.mem_flatMap.mpr ⟨l, hl, hk⟩

private theorem move_to_signed {p q : Config n V} (h : Move c χ p q) :
    DeciENSSE.Core.Move (signedSys c χ) (assoc p) (assoc q) := by
  cases h with
  | copyPlus hl => exact .copy (signed_mem hl (by simp [signedLit]))
  | copyMinus hl => exact .copy (signed_mem hl (by simp [signedLit]))
  | @flePush a u w i hl =>
    exact DeciENSSE.Core.Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fle (fun j => (a j, c j)) (u, false) ∈
        signedLit c (.fle a u) by simp [signedLit]))
  | @flePop a u w i hl =>
    exact DeciENSSE.Core.Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.lef (u, true) (fun j => (a j, !(c j))) ∈
        signedLit c (.fle a u) by simp [signedLit]))
  | @lefPop u a w i hl =>
    exact DeciENSSE.Core.Move.pop (w := w) i (signed_mem (c := c) hl
      (show Lit.lef (u, false) (fun j => (a j, c j)) ∈
        signedLit c (.lef u a) by simp [signedLit]))
  | @lefPush u a w i hl =>
    exact DeciENSSE.Core.Move.push (w := w) i (signed_mem (c := c) hl
      (show Lit.fle (fun j => (a j, !(c j))) (u, true) ∈
        signedLit c (.lef u a) by simp [signedLit]))

private theorem signed_to_move {p q : DeciENSSE.Core.Config n (V × Bool)}
    (h : DeciENSSE.Core.Move (signedSys c χ) p q) :
    Move c χ (assoc.symm p) (assoc.symm q) := by
  cases h with
  | copy hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, List.not_mem_nil,
      or_false, Lit.le.injEq, reduceCtorEq] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .copyPlus hsrc
    · exact .copyMinus hsrc
  | push i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, List.not_mem_nil,
      or_false, false_or, Lit.fle.injEq, reduceCtorEq] at hk
    all_goals rcases hk with ⟨rfl, rfl⟩
    · exact .flePush (c := c) i hsrc
    · exact .lefPush (c := c) i hsrc
  | pop i hl =>
    obtain ⟨l, hsrc, hk⟩ := List.mem_flatMap.mp hl
    cases l <;> simp only [signedLit, List.mem_cons, List.not_mem_nil,
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
      Bound.Moves (signedSys c χ) (assoc p) (assoc q) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hm ih => exact .step ih (move_to_signed hm)
  · intro h
    have lift {a b} (hh : Bound.Moves (signedSys c χ) a b) :
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

/-- The bot case makes this total; signed systems never contain bot. -/
def dualLit : Lit n (V × Bool) → Lit n (V × Bool)
  | .le x y => .le (flipV y) (flipV x)
  | .fle a u => .lef (flipV u) (fun i => flipV (a i))
  | .lef u a => .fle (fun i => flipV (a i)) (flipV u)
  | .bot u => .bot (flipV u)

/-- Signed paths reverse under sign flip. -/
theorem signed_dual {l : Lit n (V × Bool)} (h : l ∈ signedSys c χ) :
    dualLit l ∈ signedSys c χ := by
  obtain ⟨k, hk, hl⟩ := List.mem_flatMap.mp h
  apply signed_mem hk
  cases k <;> simp [signedLit] at hl ⊢
  all_goals rcases hl with rfl | rfl <;> simp [dualLit, flipV]

/-- Variance accumulated along a word (independent of the variable). -/
abbrev parityC (c : Fin n → Bool) : List (Fin n) → Bool := DeciNSSE.polarity c

/-- The empty word leaves the sign unchanged. -/
@[simp] theorem parityC_nil (c : Fin n → Bool) : parityC c [] = false := rfl

/-- Prepending a child combines its variance with the remaining parity. -/
@[simp] theorem parityC_cons (c : Fin n → Bool) (i : Fin n) (w : List (Fin n)) :
    parityC c (i :: w) = Bool.xor (c i) (parityC c w) := rfl

/-- Word concatenation composes parity changes. -/
theorem parityC_append (c : Fin n → Bool) (u v : List (Fin n)) :
    parityC c (u ++ v) = Bool.xor (parityC c u) (parityC c v) := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih]

/-- Every pure move preserves sign xor remaining-word parity. -/
theorem move_sign {p q : Config n V} (h : Move c χ p q) :
    Bool.xor q.2.1 (parityC c q.2.2) =
      Bool.xor p.2.1 (parityC c p.2.2) := by
  cases h <;> simp

/-- A pure path preserves the variance-adjusted sign. -/
theorem moves_sign {p q : Config n V}
    (h : Relation.ReflTransGen (Move c χ) p q) :
    Bool.xor q.2.1 (parityC c q.2.2) =
      Bool.xor p.2.1 (parityC c p.2.2) := by
  induction h with
  | refl => rfl
  | tail _ hm ih => exact (move_sign hm).trans ih

section Automata
variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem deriv_dual {x y : V × Bool}
    (h : Bound.Deriv (signedSys c χ) x y) :
    Bound.Deriv (signedSys c χ) (flipV y) (flipV x) := by
  induction h with
  | refl => exact .refl _
  | copy hl => exact .copy (signed_dual hl)
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁
  | decomp i hl _ hu ih =>
    exact Bound.Deriv.decomp i (signed_dual hu) ih (signed_dual hl)

/-- Sign flip reverses the saturated summary relation. -/
theorem D_dual {x y : V × Bool} :
    (x, y) ∈ Bound.D (signedSys c χ) ↔
      (flipV y, flipV x) ∈ Bound.D (signedSys c χ) := by
  constructor
  · exact fun h => Bound.mem_D_iff.mpr (deriv_dual (Bound.mem_D_iff.mp h))
  · intro h
    simpa using Bound.mem_D_iff.mpr (deriv_dual (Bound.mem_D_iff.mp h))

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
    Bound.down (signedSys c χ) (flipV y) =
      (Bound.up (signedSys c χ) y).map flipEmb := by
  ext x
  simp only [Bound.mem_down, mem_map_flip, Bound.mem_up]
  simpa using (D_dual (x := x) (y := flipV y))

/-- A lower-reader step is a flipped upper-reader step. -/
theorem qstep_flip (S : Finset (V × Bool)) (i : Fin n) :
    Bound.qstep (signedSys c χ) (S.map flipEmb) i =
      (Bound.pstep (signedSys c χ) S i).map flipEmb := by
  ext x
  simp only [Bound.mem_qstep, mem_map_flip, Bound.mem_pstep]
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
    Bound.Q (signedSys c χ) (flipV y) w =
      (Bound.P (signedSys c χ) y w).map flipEmb := by
  induction w using List.reverseRecOn with
  | nil => exact down_flip y
  | append_singleton w i ih => rw [Bound.Q_snoc, Bound.P_snoc, ih, qstep_flip]

/-- Upper summaries characterize paths to the empty word. -/
theorem mem_P_iff_moves {x r : V × Bool} (β : List (Fin n)) :
    r ∈ Bound.P (signedSys c χ) x β ↔
      Bound.Moves (signedSys c χ) (x, β) (r, []) := by
  have h := Bound.summaries_P (χ := signedSys c χ) (x := x) (b := r) β []
  simpa only [List.append_nil] using h.trans
    (Bound.above_iff (u := β) (v := []) (σ := []))

omit [Fintype V] [DecidableEq V] in
private theorem signed_lef_neg {r : V × Bool} {a : Fin n → V × Bool}
    (h : Lit.lef r a ∈ signedSys c χ) : Neg χ (r.1, r.2, []) := by
  obtain ⟨l, hl, hk⟩ := List.mem_flatMap.mp h
  cases l <;> simp only [signedLit, List.mem_cons, List.not_mem_nil,
    or_false, false_or, Lit.lef.injEq, reduceCtorEq] at hk
  all_goals rcases hk with ⟨rfl, rfl⟩
  · exact .fle hl
  · exact .lef hl

/-- Root variables obtainable by popping a signed word. -/
theorem popRoot {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Bound.P (signedSys c χ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Bound.P (signedSys c χ) x β, Neg χ (r.1, r.2, []) := by
  obtain ⟨a, ha⟩ := h
  rw [Bound.P_snoc, Bound.mem_pstep] at ha
  obtain ⟨r, hr, a, hl, _⟩ := ha
  exact ⟨r, hr, signed_lef_neg hl⟩

/-- The empty-word upper summary absorbs further summary closure. -/
theorem P_nil_absorb {x : V × Bool} {β : List (Fin n)}
    (h : Bound.P (signedSys c χ) x β = ∅) (γ : List (Fin n)) :
    Bound.P (signedSys c χ) x (β ++ γ) = ∅ := by
  induction γ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w i ih => rw [← List.append_assoc, Bound.P_snoc, ih, Bound.pstep_empty]

/-- A pure path factors through its lowest word position. -/
theorem lowest_point_leaf {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c χ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Bound.P (signedSys c χ) (p, s) (u.take i) ∩
          Bound.Q (signedSys c χ) (q, s') (t.take e)).Nonempty := by
  rw [moves_iff_signed]
  exact Bound.lowest_point

/-- All variables in one upper state have the same sign. -/
theorem sign_coherent {p : V} {s : Bool} {r : V × Bool} {w : List (Fin n)}
    (h : r ∈ Bound.P (signedSys c χ) (p, s) w) :
    r.2 = Bool.xor s (DeciNSSE.polarity c w) := by
  have hm := (mem_P_iff_moves w).mp h
  have hh : Relation.ReflTransGen (Move c χ) (p, s, w) (r.1, r.2, []) :=
    moves_iff_signed.mpr hm
  simpa using moves_sign hh

end Automata

namespace SignedExamples

/-- A ternary variance with two contravariant children. -/
abbrev arrow : Fin 3 → Bool := LeafHornExamples.arrow
/-- A ternary mixed constructor constraint. -/
abbrev mixed : List (LitT 3 Bool) := LeafHornExamples.mixed

/-- The copy case at ternary mixed variance. -/
theorem arrow_le (u v : V) : signedLit arrow (.le u v) =
    [.le (u, false) (v, false), .le (v, true) (u, true)] := rfl

/-- The signed translation of a lower constructor bound. -/
theorem arrow_fle (a : Fin 3 → V) (u : V) : signedLit arrow (.fle a u) =
    [.fle (fun i => (a i, arrow i)) (u, false),
      .lef (u, true) (fun i => (a i, !(arrow i)))] := rfl

/-- The signed translation of an upper constructor bound. -/
theorem arrow_lef (u : V) (a : Fin 3 → V) : signedLit arrow (.lef u a) =
    [.lef (u, false) (fun i => (a i, arrow i)),
      .fle (fun i => (a i, !(arrow i))) (u, true)] := rfl

/-- Extreme literals contribute no signed moves. -/
theorem arrow_constants (u : V) :
    signedLit arrow (.bot u) = [] ∧ signedLit arrow (.top u) = [] := ⟨rfl, rfl⟩

/-- The translated mixed system has the displayed two clauses. -/
theorem mixed_system : signedSys arrow mixed =
    [.lef (false, false) (fun i => (true, arrow i)),
      .fle (fun i => (true, !(arrow i))) (false, true)] := rfl

/-- All six constructor moves, including child 2, match the covariant system. -/
theorem mixed_moves (p q : Config 3 Bool) :
    DeciENSSE.Core.Move (signedSys arrow mixed) (assoc p) (assoc q) ↔
      LeafHornExamples.ArrowMoves p q :=
  move_iff_signed.symm.trans (LeafHornExamples.mixed_moves_iff p q)

/-- The mixed system has no joint parity assignment. -/
theorem mixed_no_joint : ¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
    s (.inl true) = Bool.xor (s (.inl false)) (arrow i) :=
  LeafHornExamples.mixed_no_joint

/-- The mixed system nevertheless has a satisfying assignment. -/
theorem mixed_satisfiable : ∃ ρ, SatT arrow ρ mixed :=
  ⟨LeafHornExamples.low, LeafHornExamples.low_solution⟩

/-- A concrete signed pop in the mixed system. -/
theorem mixed_pop (i : Fin 3) :
    (true, arrow i) ∈ Bound.P (signedSys arrow mixed) (false, false) [i] := by
  apply (mem_P_iff_moves [i]).mpr
  apply (moves_iff_signed (p := (false, false, [i])) (q := (true, arrow i, []))).mp
  exact Relation.ReflTransGen.single (.lefPop (a := fun _ => true) i
    (by simp [mixed, LeafHornExamples.mixed]))

/-- The concrete pop reaches the displayed root variable. -/
theorem mixed_popRoot (i : Fin 3) :
    ∃ r ∈ Bound.P (signedSys arrow mixed) (false, false) [],
      Neg mixed (r.1, r.2, []) :=
  popRoot (β := []) ⟨(true, arrow i), mixed_pop i⟩

/-- A concrete signed push in the mixed system. -/
theorem mixed_push (i : Fin 3) :
    (true, !(arrow i)) ∈ Bound.Q (signedSys arrow mixed) (false, true) [i] := by
  change (true, !(arrow i)) ∈
    Bound.Q (signedSys arrow mixed) (flipV (false, false)) [i]
  rw [Q_flip, mem_map_flip]
  simpa [flipV] using mixed_pop i

/-- The concrete paths obey sign coherence. -/
theorem mixed_coherent (i : Fin 3) {r : Bool × Bool}
    (h : r ∈ Bound.P (signedSys arrow mixed) (false, false) [i]) : r.2 = arrow i := by
  simpa using sign_coherent h

/-- The absorption premise is inhabited: no rules consume the first letter. -/
theorem empty_absorption (x : Bool × Bool) (i : Fin 3) (w : List (Fin 3)) :
    Bound.P (signedSys arrow ([] : List (LitT 3 Bool))) x ([i] ++ w) = ∅ := by
  apply P_nil_absorb (β := [i])
  rw [show [i] = [] ++ [i] from rfl, Bound.P_snoc]
  ext r
  simp [Bound.mem_pstep, signedSys]

/-- The concrete path factors through a common lowest point. -/
theorem mixed_lowest_point (i : Fin 3) :
    ∃ k ≤ ([i] : List (Fin 3)).length, ∃ e ≤ ([] : List (Fin 3)).length,
      ([i] : List (Fin 3)).drop k = ([] : List (Fin 3)).drop e ∧
        (Bound.P (signedSys arrow mixed) (false, false) ([i].take k) ∩
          Bound.Q (signedSys arrow mixed) (true, arrow i) ([].take e)).Nonempty := by
  apply lowest_point_leaf.mp
  exact Relation.ReflTransGen.single (.lefPop (a := fun _ => true) i
    (by simp [mixed, LeafHornExamples.mixed]))

/-- Kernel evaluation of the third-child upper and lower states. -/
theorem third_child_P :
    Bound.P (signedSys arrow mixed) (false, false) [2] = {(true, true)} := by
  decide +kernel

/-- The lower summary handles the third child with its flipped sign. -/
theorem third_child_Q :
    Bound.Q (signedSys arrow mixed) (false, true) [2] = {(true, false)} := by
  decide +kernel

/-- Nullary constructors produce no pure moves on either side of the translation. -/
theorem nullary_no_moves (c : Fin 0 → Bool) (p q : Config 0 Unit) :
    ¬ DeciENSSE.Core.Move (signedSys c [.fle Fin.elim0 (), .lef () Fin.elim0])
      (assoc p) (assoc q) := by
  rw [← move_iff_signed]
  exact LeafHornExamples.nullary_no_moves c p q

end SignedExamples

end DeciENSSE.Core.Mixed
