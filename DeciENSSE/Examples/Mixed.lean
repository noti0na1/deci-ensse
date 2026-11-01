import DeciENSSE.Examples.Fixtures
import DeciENSSE.Core.Mixed.Leaf
import DeciENSSE.Core.Mixed.LeafHorn
import DeciENSSE.Core.Mixed.Signed
import DeciENSSE.Core.Mixed.Duality
import DeciENSSE.Core.Mixed.Sat
import DeciENSSE.Core.Mixed.Conditions
import DeciENSSE.Core.Mixed.Membership
import DeciENSSE.Core.Mixed.Extract
import DeciENSSE.Core.Mixed.CondI0
import DeciENSSE.Core.Mixed.Units
import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Core.Mixed.Final
import DeciENSSE.Core.Mixed.Regular
import DeciENSSE.Core.Mixed.Finite

/-! # Mixed-signature examples

Concrete leaf cones, seeds, units, self events, and entailment decisions exercise
the variance layer. A joint parity assignment chooses one sign for each variable
so every child edge changes sign by its declared variance. The ternary examples
contain both covariant and contravariant edges between the same variables, so
such an assignment cannot exist; the signed-copy construction still applies.

## Main declarations

The example namespaces below give unary, ternary, and nullary instances.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

namespace LeafExamples

/-- The third contravariant child flips the sign; extension past a leaf does not. -/
theorem ternary_third_child (w : List (Fin 3)) :
    2 :: w ∈ leaf ![true, false, true]
      (DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.bot)) false := by
  simp

/-- Two finite inputs have an infinite information intersection. -/
theorem ternary_infoInter_not_finite (c : Fin 3 → Bool) :
    infoInter c DeciNSSE.Tree.bot DeciNSSE.Tree.top = (RGraph.allF 3).unfold ∧
      ¬ ∃ a : FTree 3, a.toTree = infoInter c DeciNSSE.Tree.bot DeciNSSE.Tree.top := by
  rw [infoInter_bot_top]
  exact ⟨rfl, allF_not_finite 0⟩

/-- At arity zero the same intersection is the finite nullary constructor. -/
theorem nullary_infoInter (c : Fin 0 → Bool) :
    infoInter c DeciNSSE.Tree.bot DeciNSSE.Tree.top = (FTree.node Fin.elim0).toTree := by
  rw [infoInter_bot_top, RGraph.allF_unfold_node, FTree.toTree_node]
  congr 1
  funext i
  exact Fin.elim0 i

end LeafExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

namespace LeafHornExamples

/-- Two contravariant children and one covariant child. -/
def ternaryVariance : Fin 3 → Bool := ![true, false, true]

/-- `false` names y and `true` names z; the child variable is repeated. -/
def ternaryLit : List (LitT 3 Bool) := [.lef false (fun _ => true)]

/-- Exactly two implications for each of the three children. -/
def ArrowMoves (p q : Config 3 Bool) : Prop := ∃ (i : Fin 3) (w : List (Fin 3)),
  (p = (false, false, i :: w) ∧ q = (true, ternaryVariance i, w)) ∨
  (p = (true, !(ternaryVariance i), w) ∧ q = (false, true, i :: w))

/-- The ternary example has exactly the displayed literal moves. -/
theorem mixed_moves_iff (p q : Config 3 Bool) :
    Move ternaryVariance ternaryLit p q ↔ ArrowMoves p q := by
  constructor
  · intro h
    cases h with
    | copyPlus hl => simp [ternaryLit] at hl
    | copyMinus hl => simp [ternaryLit] at hl
    | flePush i hl => simp [ternaryLit] at hl
    | flePop i hl => simp [ternaryLit] at hl
    | @lefPop u a w i hl =>
      simp only [ternaryLit, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      exact ⟨i, w, Or.inl ⟨rfl, rfl⟩⟩
    | @lefPush u a w i hl =>
      simp only [ternaryLit, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      exact ⟨i, w, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨i, w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact .lefPop (a := fun _ => true) i (by simp [ternaryLit])
    · exact .lefPush (a := fun _ => true) i (by simp [ternaryLit])

/-- Its clauses are literal moves or right extensions. -/
theorem mixed_clause_iff (p q : Config 3 Bool) : Clause ternaryVariance ternaryLit p q ↔
    ArrowMoves p q ∨ ∃ v s w i, p = (v, s, w) ∧ q = (v, s, w ++ [i]) := by
  constructor
  · intro h
    cases h with
    | move hm => exact Or.inl ((mixed_moves_iff _ _).mp hm)
    | extend v s w i => exact Or.inr ⟨v, s, w, i, rfl, rfl⟩
  · rintro (hm | ⟨v, s, w, i, rfl, rfl⟩)
    · exact .move ((mixed_moves_iff _ _).mpr hm)
    · exact .extend v s w i

/-- The ternary example forbids exactly the displayed root atom. -/
theorem mixed_neg_iff (p : Config 3 Bool) : Neg ternaryLit p ↔ p = (false, false, []) := by
  constructor
  · intro h
    cases h with
    | fle hl => simp [ternaryLit] at hl
    | lef hl =>
      simp only [ternaryLit, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩; rfl
  · rintro rfl; exact .lef (a := fun _ => true) (by simp [ternaryLit])

/-- The ternary constructor example has no positive units. -/
theorem mixed_no_facts (p : Config 3 Bool) : ¬ Fact ternaryLit p := by
  intro h
  cases h with
  | bot hl => simp [ternaryLit] at hl
  | top hl => simp [ternaryLit] at hl

/-- The exact parity equations for this literal are inconsistent. -/
theorem mixed_no_parity : ¬ ∃ s : Bool → Bool, ∀ i : Fin 3,
    s true = Bool.xor (s false) (ternaryVariance i) := by
  rintro ⟨s, hs⟩
  have h0 := hs 0
  have h1 := hs 1
  change s true = Bool.xor (s false) true at h0
  change s true = Bool.xor (s false) false at h1
  have h := h0.symm.trans h1
  cases hy : s false <;> simp [hy] at h

/-- The empty antecedent cannot repair the consequent's parity equations. -/
theorem mixed_no_joint : ¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
    s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i) := by
  rintro ⟨s, hs⟩
  exact mixed_no_parity ⟨s ∘ Sum.inl, hs⟩

/-- The constant bottom assignment. -/
def low : Bool → Tree 3 := fun _ => DeciNSSE.Tree.bot

/-- A bottom assignment with one constructor root. -/
def branch : Bool → Tree 3 :=
  fun i => if i then DeciNSSE.Tree.bot else DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.bot)

/-- The constant bottom assignment solves the mixed example. -/
theorem low_solution : SatT ternaryVariance low ternaryLit := by simp [SatT, HoldsT, ternaryLit,
  low]

/-- The constructor assignment solves the mixed example. -/
theorem branch_solution : SatT ternaryVariance branch ternaryLit := by
  simp [SatT, HoldsT, ternaryLit, branch, Function.comp_def, treeLe_refl]

/-- Two distinct solutions and their information intersection. -/
theorem mixed_infoInter_solution :
    SatT ternaryVariance (fun v => infoInter ternaryVariance (low v) (branch v)) ternaryLit :=
  sat_infoInter low_solution branch_solution

/-- The mixed example's information intersection has intersected cones. -/
theorem mixed_infoInter_coordinates (v s : Bool) :
    leaf ternaryVariance (infoInter ternaryVariance (low v) (branch v)) s =
      leaf ternaryVariance (low v) s ∩ leaf ternaryVariance (branch v) s := leaf_infoInter ..

/-- The two displayed satisfying assignments differ. -/
theorem solutions_distinct : low ≠ branch := by
  intro h
  have he := congrFun h false
  exact DeciNSSE.Tree.node_ne_bot _ he.symm

/-- Non-vacuity of all five forms and both sorts of negative root units. -/
theorem all_forms_sol (c : Fin n → Bool) :
    Sol c [.le 0 1, .fle (fun _ => 0) 1, .lef 0 (fun _ => 1), .bot 0, .top 1]
      (configSet c (fun x : Fin 2 => if x = 0 then DeciNSSE.Tree.bot
        else DeciNSSE.Tree.top : Fin 2 → Tree n)) := by
  apply (sat_iff_sol _).mp
  simp [SatT, HoldsT]

/-- Non-vacuity of the three least-extension checks, without joint parity. -/
theorem mixed_extension_checks :
    let ψ : List (LitT 3 (Bool ⊕ Unit)) := [.lef (.inl false) (fun _ => .inl true)]
    let S := Hull ternaryVariance ψ (visibleSeeds ternaryVariance low)
    Avoids ψ S ∧ Consistent S ∧ restrict S ⊆ configSet ternaryVariance low := by
  apply (extends_iff_hull _ _).mp
  exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, low]⟩

/-- All four constructor rule forms act on child 2, with the correct flipped signs. -/
theorem third_child_rules (w : List (Fin 3)) :
    Move ternaryVariance [.fle (fun _ => true) false]
      (true, true, w) (false, false, 2 :: w) ∧
    Move ternaryVariance [.fle (fun _ => true) false]
      (false, true, 2 :: w) (true, false, w) ∧
    Move ternaryVariance ternaryLit (false, false, 2 :: w) (true, true, w) ∧
    Move ternaryVariance ternaryLit (true, false, w) (false, true, 2 :: w) := by
  exact ⟨.flePush (a := fun _ => true) 2 (by simp),
    .flePop (a := fun _ => true) 2 (by simp),
    .lefPop (a := fun _ => true) 2 (by simp [ternaryLit]),
    .lefPush (a := fun _ => true) 2 (by simp [ternaryLit])⟩

/-- With no children, constructor literals contribute only their root exclusions. -/
theorem nullary_no_moves (c : Fin 0 → Bool) (p q : Config 0 Unit) :
    ¬ Move c [.fle Fin.elim0 (), .lef () Fin.elim0] p q := by
  intro h
  cases h with
  | copyPlus hl => simp at hl
  | copyMinus hl => simp at hl
  | flePush i _ => exact Fin.elim0 i
  | flePop i _ => exact Fin.elim0 i
  | lefPop i _ => exact Fin.elim0 i
  | lefPush i _ => exact Fin.elim0 i

/-- Nullary constructor literals have a satisfying Horn presentation. -/
theorem nullary_constructor_solution (c : Fin 0 → Bool) :
    Sol c [.fle Fin.elim0 (), .lef () Fin.elim0]
      (configSet c (fun _ : Unit => DeciNSSE.Tree.node Fin.elim0)) := by
  apply (sat_iff_sol _).mp
  simp [SatT, HoldsT, treeLe_refl]

end LeafHornExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words
open DeciNSSE DeciENSSE.Core.Full
variable {n : ℕ} {V : Type*}

namespace SignedExamples

/-- A ternary variance with two contravariant children. -/
abbrev ternaryVariance : Fin 3 → Bool := LeafHornExamples.ternaryVariance
/-- A ternary mixed constructor constraint. -/
abbrev ternaryLit : List (LitT 3 Bool) := LeafHornExamples.ternaryLit

/-- The copy case at ternary mixed variance. -/
theorem arrow_le (u v : V) : signedMovesLit ternaryVariance (.le u v) =
    [.le (u, false) (v, false), .le (v, true) (u, true)] := rfl

/-- The signed translation of a lower constructor bound. -/
theorem arrow_fle (a : Fin 3 → V) (u : V) : signedMovesLit ternaryVariance (.fle a u) =
    [.fle (fun i => (a i, ternaryVariance i)) (u, false),
      .lef (u, true) (fun i => (a i, !(ternaryVariance i)))] := rfl

/-- The signed translation of an upper constructor bound. -/
theorem arrow_lef (u : V) (a : Fin 3 → V) : signedMovesLit ternaryVariance (.lef u a) =
    [.lef (u, false) (fun i => (a i, ternaryVariance i)),
      .fle (fun i => (a i, !(ternaryVariance i))) (u, true)] := rfl

/-- Extreme literals contribute no signed moves. -/
theorem arrow_constants (u : V) :
    signedMovesLit ternaryVariance (.bot u) = [] ∧
      signedMovesLit ternaryVariance (.top u) = [] := ⟨rfl, rfl⟩

/-- The translated mixed system has the displayed two clauses. -/
theorem mixed_system : signedSys ternaryVariance ternaryLit =
    [.lef (false, false) (fun i => (true, ternaryVariance i)),
      .fle (fun i => (true, !(ternaryVariance i))) (false, true)] := rfl

/-- All six constructor moves, including child 2, match the covariant system. -/
theorem mixed_moves (p q : Config 3 Bool) :
    DeciENSSE.Core.Move (signedSys ternaryVariance ternaryLit) (assoc p) (assoc q) ↔
      LeafHornExamples.ArrowMoves p q :=
  move_iff_signed.symm.trans (LeafHornExamples.mixed_moves_iff p q)

/-- The mixed system has no joint parity assignment. -/
theorem mixed_no_joint : ¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
    s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i) :=
  LeafHornExamples.mixed_no_joint

/-- The mixed system nevertheless has a satisfying assignment. -/
theorem mixed_satisfiable : ∃ ρ, SatT ternaryVariance ρ ternaryLit :=
  ⟨LeafHornExamples.low, LeafHornExamples.low_solution⟩

/-- A concrete signed pop in the mixed system. -/
theorem mixed_pop (i : Fin 3) :
    (true, ternaryVariance i) ∈ Automata.P (signedSys ternaryVariance ternaryLit) (false, false)
      [i] := by
  apply (mem_P_iff_moves [i]).mpr
  apply (moves_iff_signed (p := (false, false, [i])) (q := (true, ternaryVariance i, []))).mp
  exact Relation.ReflTransGen.single (.lefPop (a := fun _ => true) i
    (by simp [ternaryLit, LeafHornExamples.ternaryLit]))

/-- The concrete pop reaches the displayed root variable. -/
theorem mixed_popRoot (i : Fin 3) :
    ∃ r ∈ Automata.P (signedSys ternaryVariance ternaryLit) (false, false) [],
      Neg ternaryLit (r.1, r.2, []) :=
  popRoot (β := []) ⟨(true, ternaryVariance i), mixed_pop i⟩

/-- A concrete signed push in the mixed system. -/
theorem mixed_push (i : Fin 3) :
    (true, !(ternaryVariance i)) ∈ Automata.Q (signedSys ternaryVariance ternaryLit) (false, true)
      [i] := by
  change (true, !(ternaryVariance i)) ∈
    Automata.Q (signedSys ternaryVariance ternaryLit) (flipV (false, false)) [i]
  rw [Q_flip, mem_map_flip]
  simpa [flipV] using mixed_pop i

/-- The concrete paths obey sign coherence. -/
theorem mixed_coherent (i : Fin 3) {r : Bool × Bool}
    (h : r ∈ Automata.P (signedSys ternaryVariance ternaryLit) (false, false) [i]) : r.2 =
      ternaryVariance i := by
  simpa using sign_coherent h

/-- The absorption premise is inhabited: no rules consume the first letter. -/
theorem empty_absorption (x : Bool × Bool) (i : Fin 3) (w : List (Fin 3)) :
    Automata.P (signedSys ternaryVariance ([] : List (LitT 3 Bool))) x ([i] ++ w) = ∅ := by
  apply P_nil_absorb (β := [i])
  rw [show [i] = [] ++ [i] from rfl, Automata.P_snoc]
  ext r
  simp [Automata.mem_pstep, signedSys]

/-- The concrete path factors through a common lowest point. -/
theorem mixed_lowest_point (i : Fin 3) :
    ∃ k ≤ ([i] : List (Fin 3)).length, ∃ e ≤ ([] : List (Fin 3)).length,
      ([i] : List (Fin 3)).drop k = ([] : List (Fin 3)).drop e ∧
        (Automata.P (signedSys ternaryVariance ternaryLit) (false, false) ([i].take k) ∩
          Automata.Q (signedSys ternaryVariance ternaryLit) (true, ternaryVariance i) ([].take
            e)).Nonempty := by
  apply lowest_point_leaf.mp
  exact Relation.ReflTransGen.single (.lefPop (a := fun _ => true) i
    (by simp [ternaryLit, LeafHornExamples.ternaryLit]))

/-- Kernel evaluation of the third-child upper and lower states. -/
theorem third_child_P :
    Automata.P (signedSys ternaryVariance ternaryLit) (false, false) [2] = {(true, true)} := by
  decide +kernel

/-- The lower summary handles the third child with its flipped sign. -/
theorem third_child_Q :
    Automata.Q (signedSys ternaryVariance ternaryLit) (false, true) [2] = {(true, false)} := by
  decide +kernel

/-- Nullary constructors produce no pure moves on either side of the translation. -/
theorem nullary_no_moves (c : Fin 0 → Bool) (p q : Config 0 Unit) :
    ¬ DeciENSSE.Core.Move (signedSys c [.fle Fin.elim0 (), .lef () Fin.elim0])
      (assoc p) (assoc q) := by
  rw [← move_iff_signed]
  exact LeafHornExamples.nullary_no_moves c p q

end SignedExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {χ : List (LitT n V)}

namespace DualityExamples
open LeafHornExamples

/-- The mixed constructor example is satisfiable. -/
theorem mixed_sat : ∃ ρ, SatT ternaryVariance ρ ternaryLit := ⟨low, low_solution⟩

/-- The mixed example has empty unit closure. -/
theorem mixed_mu_empty : Mu ternaryVariance ternaryLit = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨a, ha, _⟩ := mem_mu.mp hb
  exact mixed_no_facts a ha

/-- The background premise is inhabited even without joint parity. -/
theorem mixed_background :
    Avoids ternaryLit (Mu ternaryVariance ternaryLit) ∧
      Consistent (Mu ternaryVariance ternaryLit) :=
  sat_iff_mu.mp mixed_sat

/-- The ternary example admits no joint parity assignment. -/
theorem no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    ∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i) := mixed_no_joint

/-- The two branches collide at z at the empty word. -/
theorem mixed_collision :
    Reach ternaryVariance ternaryLit (false, false, [1]) (true, false, []) ∧
    Reach ternaryVariance ternaryLit (false, false, [0]) (true, true, []) := by
  constructor
  · exact .step .refl (.move (.lefPop (a := fun _ => true) 1 (by simp [ternaryLit])))
  · exact .step .refl (.move (.lefPop (a := fun _ => true) 0 (by simp [ternaryLit])))

/-- The `ternaryLit` return path is y⁺(1) → z⁺(ε) → y⁻(0). -/
theorem mixed_return : Moves ternaryVariance ternaryLit (false, false, [1]) (false, true, [0]) := by
  have h : Move ternaryVariance ternaryLit (false, false, [1]) (true, false, []) :=
    .lefPop (a := fun _ => true) 1 (by simp [ternaryLit])
  exact (Relation.ReflTransGen.single h).tail
    (.lefPush (a := fun _ => true) 0 (by simp [ternaryLit]))

/-- The mixed example has a return to an opposite signed atom. -/
theorem mixed_collision_return :
    ∃ δ, Reach ternaryVariance ternaryLit (false, false, [1]) (false, true, [0] ++ δ) :=
  collision_return mixed_collision.1 mixed_collision.2

/-- The third child participates in the collision and opposite-sign return. -/
theorem third_child_return :
    Reach ternaryVariance ternaryLit (false, false, [2]) (true, true, []) ∧
    Moves ternaryVariance ternaryLit (false, false, [1]) (false, true, [2]) := by
  refine ⟨.step .refl (.move (.lefPop (a := fun _ => true) 2 (by simp [ternaryLit]))), ?_⟩
  have h : Move ternaryVariance ternaryLit (false, false, [1]) (true, false, []) :=
    .lefPop (a := fun _ => true) 1 (by simp [ternaryLit])
  exact (Relation.ReflTransGen.single h).tail
    (.lefPush (a := fun _ => true) 2 (by simp [ternaryLit]))

/-- The first seed alone is live, using the branching solution. -/
theorem mixed_zero_live : Live ternaryVariance ternaryLit (false, false, [0]) := by
  refine ⟨configSet ternaryVariance branch, (sat_iff_sol _).mp branch_solution, ?_⟩
  simp [configSet, branch, ternaryVariance]

/-- The second seed alone is live as well. -/
theorem mixed_one_live : Live ternaryVariance ternaryLit (false, false, [1]) := by
  let ρ : Bool → Tree 3 := fun i =>
    if i then DeciNSSE.Tree.top else DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.top)
  have hρ : SatT ternaryVariance ρ ternaryLit := by
    simp [SatT, HoldsT, ternaryLit, ρ, Function.comp_def, treeLe_refl]
  refine ⟨configSet ternaryVariance ρ, (sat_iff_sol _).mp hρ, ?_⟩
  simp [configSet, ρ, ternaryVariance]

/-- Singleton liveness is not joint liveness: the return path exposes the conflict. -/
theorem mixed_not_jointly_live : ¬ ∃ S, Sol ternaryVariance ternaryLit S ∧
    (false, false, [0]) ∈ S ∧ (false, false, [1]) ∈ S := by
  rintro ⟨S, hS, hzero, hone⟩
  exact hS.consistent (.pair false [0]) hzero
    ((moves_reach mixed_return).mem_of_closed hS.closed hone)

/-- First deadness case: the forbidden constructor root itself. -/
theorem negative_root_witness :
    ∃ n, Neg ternaryLit n ∧ Reach ternaryVariance ternaryLit (false, false, []) n :=
  ⟨(false, false, []), .lef (a := fun _ => true) (by simp [ternaryLit]), .refl⟩

/-- A forbidden root atom is not live. -/
theorem negative_root_dead : ¬ Live ternaryVariance ternaryLit (false, false, []) :=
  (dead_iff mixed_background).mpr (Or.inl negative_root_witness)

/-- Second deadness case: a positive unit supplies the opposite descendant. -/
def forced : List (LitT 3 Unit) := [.bot ()]

/-- The forced-unit example is satisfiable. -/
theorem forced_sat : ∃ ρ, SatT ternaryVariance ρ forced := by
  exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, forced]⟩

/-- Unit closure contains the opposite signed atom. -/
theorem forced_opposite (u : List (Fin 3)) : ((), true, u) ∈ Mu ternaryVariance forced := by
  apply mem_mu.mpr
  exact ⟨((), true, []), .bot (by simp [forced]), by simpa using
    (reach_extend (c := ternaryVariance) (χ := forced) () true [] u)⟩

/-- An atom opposite a forced unit is dead. -/
theorem forced_dead (u : List (Fin 3)) : ¬ Live ternaryVariance forced ((), false, u) := by
  apply (dead_iff (sat_iff_mu.mp forced_sat)).mpr
  exact Or.inr (Or.inl ⟨[], by simpa using forced_opposite u⟩)

/-- Third deadness case: x ≤ f(x,x,x) returns x⁺(0) to x⁻(0). -/
def self : List (LitT 3 Unit) := [.lef () (fun _ => ())]

/-- The self-return example is satisfiable. -/
theorem self_sat : ∃ ρ, SatT ternaryVariance ρ self :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, self]⟩

/-- The self-return example reaches its opposite atom. -/
theorem self_return : Reach ternaryVariance self ((), false, [0]) ((), true, [0]) := by
  exact .step (.step .refl (.move (.lefPop (a := fun _ => ()) 0 (by simp [self]))))
    (.extend () true [] 0)

/-- The self-return seed is dead. -/
theorem self_dead : ¬ Live ternaryVariance self ((), false, [0]) := by
  apply (dead_iff (sat_iff_mu.mp self_sat)).mpr
  exact Or.inr (Or.inr ⟨[], by simpa using self_return⟩)

end DualityExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words

variable {n : ℕ}
open DeciENSSE.Core.Full

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

namespace SatMixedExamples
open LeafHornExamples

/-- A satisfiable system that has no joint parity assignment. -/
theorem mixed_positive :
    @decide (∃ ρ, SatT ternaryVariance ρ ternaryLit) (decideSatMixed ternaryVariance ternaryLit) =
      true :=
  (decideSatMixed_true_iff _ _).mpr DualityExamples.mixed_sat

/-- A positive root unit forbidden by an upper constructor bound. -/
def rootClash : List (LitT n Unit) := [.top (), .lef () (fun _ => ())]

/-- The negative-root test has an actual obstruction, independent of consistency. -/
theorem root_not_avoids (c : Fin n → Bool) : ¬ Avoids rootClash (Mu c rootClash) := by
  intro h
  exact h (mem_mu.mpr ⟨((), false, []), .top (by simp [rootClash]), .refl⟩)
    (.lef (a := fun _ => ()) (by simp [rootClash]))

/-- Kernel evaluation of the actual root-rejection branch of the decider. -/
theorem root_negative :
    @decide (∃ ρ, SatT ternaryVariance ρ rootClash) (decideSatMixed ternaryVariance rootClash) =
      false := by
  decide +kernel

/-- Both extreme units on one variable. -/
def signClash : List (LitT n Unit) := [.top (), .bot ()]

/-- No negative units occur here; intrinsic disjointness detects the contradiction. -/
theorem sign_collision (c : Fin n → Bool) : MuCollision c signClash () [] := by
  apply (muCollision_iff _ _ _ _).mpr
  exact ⟨mem_mu.mpr ⟨((), false, []), .top (by simp [signClash]), .refl⟩,
    mem_mu.mpr ⟨((), true, []), .bot (by simp [signClash]), .refl⟩⟩

/-- Opposite extreme units introduce no negative root literals. -/
theorem sign_avoids (c : Fin n → Bool) : Avoids signClash (Mu c signClash) := by
  intro p _ hn
  cases hn <;> simp_all [signClash]

/-- The satisfiability decision rejects opposite extreme units. -/
theorem sign_negative (c : Fin n → Bool) :
    @decide (∃ ρ, SatT c ρ signClash) (decideSatMixed c signClash) = false := by
  rw [decide_eq_false_iff_not]
  intro hs
  obtain ⟨hp, hm⟩ := (muCollision_iff _ _ _ _).mp (sign_collision c)
  exact (sat_iff_mu.mp hs).2 (.pair () []) hp hm

/-- The lower summary is already empty after one edge, but the earlier hit remains. -/
theorem sticky_after_empty :
    (Automata.Q (signedSys ternaryVariance ([.top ()] : List (LitT 3 Unit))) ((), false) [2] = ∅) ∧
    ((muDFA ternaryVariance ([.top ()] : List (LitT 3 Unit)) ((), false)).run [2]).2 = true := by
  decide +kernel

/-- The executable procedure also covers the empty variable type. -/
theorem empty_variables :
    @decide (∃ ρ, SatT ternaryVariance ρ ([] : List (LitT 3 Empty)))
      (decideSatMixed ternaryVariance []) = true := by
  decide +kernel

/-- The root-rejection branch is executable even with no child letters. -/
theorem nullary_root_negative :
    @decide (∃ ρ, SatT (fun i : Fin 0 => i.elim0) ρ rootClash)
      (decideSatMixed (fun i : Fin 0 => i.elim0) rootClash) = false := by
  decide +kernel

end SatMixedExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} {c : Fin n → Bool}
  {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

namespace ConditionsExamples
open LeafHornExamples

/-- Visible `false = y`, `true = x`; each child has its own hidden variable. Distinct hidden
children keep the reached hidden signs as sinks. -/
def separate : List (LitT 3 (Bool ⊕ Fin 3)) :=
  [.lef (.inl false) Sum.inr]

/-- The empty antecedent is satisfiable. -/
theorem empty_sat : ∃ ρ : Bool → Tree 3, SatT ternaryVariance ρ [] :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT]⟩

/-- The separate-variable consequent is satisfiable. -/
theorem separate_sat : ∃ ρ, SatT ternaryVariance ρ separate :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, separate]⟩

/-- The separate-variable consequent has no forced atoms. -/
theorem separate_mu_empty : Mu ternaryVariance separate = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨a, hf, _⟩ := mem_mu.mp hb
  cases hf <;> simp_all [separate]

/-- The positive unit condition holds for the separate-variable example. -/
theorem separate_condI0 : CondI0 ternaryVariance [] separate := by
  intro a ha
  change visible a ∈ Mu ternaryVariance separate at ha
  rw [separate_mu_empty] at ha
  exact ha.elim

/-- Hidden signs reached from a visible seed are sinks: the reverse rule requires the opposite
sign at that same hidden variable. -/
def envelope (S : Set (Config 3 Bool)) : Set (Config 3 (Bool ⊕ Fin 3)) :=
  {p | match p.1 with
    | .inl x => (x, p.2) ∈ S
    | .inr i => p.2.1 = ternaryVariance i}

/-- The displayed envelope is closed under all clauses. -/
theorem envelope_closed {S : Set (Config 3 Bool)} (hS : Closed ternaryVariance [] S) :
    Closed ternaryVariance separate (envelope S) := by
  intro p q hpq hp
  cases hpq with
  | extend v s w i =>
    cases v with
    | inl x => exact hS (.extend x s w i) hp
    | inr z => exact hp
  | move hm =>
    cases hm with
    | copyPlus hl => simp [separate] at hl
    | copyMinus hl => simp [separate] at hl
    | flePush i hl => simp [separate] at hl
    | flePop i hl => simp [separate] at hl
    | lefPop i hl =>
      simp only [separate, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      rfl
    | lefPush i hl =>
      simp only [separate, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      simp [envelope] at hp

/-- Visible-to-visible paths only add structural descendants. -/
theorem separate_visible_reach {a b : Config 3 Bool}
    (hr : Reach ternaryVariance separate (visible a) (visible b)) : b ∈ Cl ternaryVariance [] a :=
      by
  exact hr.mem_of_closed (envelope_closed (hull_closed _))
    (show visible a ∈ envelope (Cl ternaryVariance [] a) from mem_cl.mpr (Or.inr .refl))

/-- The singleton closure condition holds in the separate-variable example. -/
theorem separate_condII : CondII ternaryVariance [] separate :=
  fun _ _ _ hr => separate_visible_reach hr

/-- A root atom is live over the empty antecedent. -/
theorem empty_root_live : Live ternaryVariance ([] : List (LitT 3 Bool)) (false, false, []) := by
  refine ⟨configSet ternaryVariance (fun _ => DeciNSSE.Tree.top), (sat_iff_sol _).mp ?_, ?_⟩
  · simp [SatT]
  · simp [configSet]

/-- The separate-variable example fails the negative unit condition. -/
theorem separate_not_condU : ¬ CondU ternaryVariance [] separate := by
  intro h
  exact h (false, false, []) empty_root_live (visible (false, false, []))
    (.lef (a := Sum.inr) (by simp [separate])) .refl

/-- Direct check against the tree semantics: visible y = top has no witness. -/
theorem separate_not_entails : ¬ ExistsEntailsT ternaryVariance [] separate := by
  intro h
  obtain ⟨σ, _, hσ⟩ := h (fun _ => DeciNSSE.Tree.top) (fun _ => trivial) (by simp [SatT])
  have hle := hσ (.lef (.inl false) Sum.inr) (by simp [separate])
  exact leaf_node_nil ternaryVariance σ false
    (((treeLe_iff_leaf _ _ _).mp hle).1 (by simp))

/-- All satisfiability premises hold, but dropping U makes the test unsound. -/
theorem units_cannot_be_dropped :
    (∃ ρ : Bool → Tree 3, SatT ternaryVariance ρ []) ∧
    (∃ ρ, SatT ternaryVariance ρ separate) ∧
    CondI0 ternaryVariance [] separate ∧ CondII ternaryVariance [] separate ∧
    ¬ CondU ternaryVariance [] separate ∧ ¬ ExistsEntailsT ternaryVariance [] separate :=
  ⟨empty_sat, separate_sat, separate_condI0, separate_condII,
    separate_not_condU, separate_not_entails⟩

/-- The characterization itself detects exactly the missing condition U. -/
theorem separate_characterization :
    ExistsEntailsT ternaryVariance [] separate ↔
      CondI0 ternaryVariance [] separate ∧ CondU ternaryVariance [] separate ∧ CondII
        ternaryVariance [] separate :=
  three_conditions_mixed empty_sat separate_sat

/-- Two seeds of `ternaryLit = [y ≤ f(z,z,z)]` collide via `DualityExamples.mixed_return`. -/
theorem mixed_two_seed_collision :
    Reach ternaryVariance ternaryLit (false, false, [1]) (true, false, []) ∧
    Reach ternaryVariance ternaryLit (false, false, [0]) (true, true, []) ∧
    Moves ternaryVariance ternaryLit (false, false, [1]) (false, true, [0]) :=
  ⟨DualityExamples.mixed_collision.1, DualityExamples.mixed_collision.2,
    DualityExamples.mixed_return⟩

/-- Put that same mixed constraint in the visible part of a consequent. -/
def embedded : List (LitT 3 (Bool ⊕ Unit)) :=
  [.lef (.inl false) (fun _ => .inl true)]

/-- The visible embedding of the mixed system is satisfiable. -/
theorem embedded_sat : ∃ ρ, SatT ternaryVariance ρ embedded :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, embedded]⟩

/-- The embedded mixed system admits no joint parity assignment. -/
theorem embedded_no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) := by
  rintro ⟨s, hφ⟩
  exact mixed_no_parity ⟨s ∘ Sum.inl, hφ⟩

/-- Direct semantic proof, with a satisfiable antecedent and no joint parity. -/
theorem embedded_entails : ExistsEntailsT ternaryVariance ternaryLit embedded := by
  intro ρ _ hρ
  refine ⟨fun _ => DeciNSSE.Tree.bot, fun _ => trivial, ?_⟩
  simpa [SatT, HoldsT, embedded, ternaryLit, Function.comp_def] using hρ

/-- Non-vacuity of all three conditions at mixed variance. -/
theorem embedded_conditions :
    CondI0 ternaryVariance ternaryLit embedded ∧ CondU ternaryVariance ternaryLit embedded ∧
      CondII ternaryVariance ternaryLit embedded :=
  (three_conditions_mixed DualityExamples.mixed_sat embedded_sat).mp embedded_entails

/-- Pure visible returns obey the singleton closure condition. -/
theorem embedded_pure_condition : ∀ a b : Config 3 Bool, Live ternaryVariance ternaryLit a →
    Moves ternaryVariance embedded (visible a) (visible b) → b ∈ Cl ternaryVariance ternaryLit a :=
  condII_iff_moves.mp embedded_conditions.2.2

/-- The same non-parity consequent fails over the empty antecedent. -/
theorem embedded_empty_no_joint_parity :
    ¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i) := mixed_no_joint

/-- The empty antecedent does not entail the embedded mixed system. -/
theorem embedded_empty_not_entails : ¬ ExistsEntailsT ternaryVariance [] embedded := by
  intro h
  obtain ⟨σ, _, hσ⟩ := h (fun _ => DeciNSSE.Tree.top) (fun _ => trivial) (by simp [SatT])
  have hle := hσ (.lef (.inl false) (fun _ => .inl true)) (by simp [embedded])
  exact leaf_node_nil ternaryVariance (fun _ => DeciNSSE.Tree.top) false
    (((treeLe_iff_leaf _ _ _).mp hle).1 (by simp))

/-- Both collision seeds occur in one empty-antecedent model. Neither is a root. -/
def collisionAssignment : Bool → Tree 3 :=
  fun i => if i then DeciNSSE.Tree.bot else
    DeciNSSE.Tree.node (fun i => if i = 1 then DeciNSSE.Tree.top else DeciNSSE.Tree.bot)

/-- Two distinct words occur together in the displayed assignment. -/
theorem collision_seeds :
    (false, false, [0]) ∈ configSet ternaryVariance collisionAssignment ∧
    (false, false, [1]) ∈ configSet ternaryVariance collisionAssignment := by
  simp [configSet, collisionAssignment, ternaryVariance]

/-- The embedded system returns between opposite signed visible atoms. -/
theorem embedded_return :
    Moves ternaryVariance embedded (visible (false, false, [1])) (visible (false, true, [0])) := by
  have h : Move ternaryVariance embedded (visible (false, false, [1])) (.inl true, false, []) :=
    Move.lefPop (c := ternaryVariance) (χ := embedded)
      (a := fun _ => .inl true) 1 (by simp [embedded])
  exact (Relation.ReflTransGen.single h).tail
    (Move.lefPush (c := ternaryVariance) (χ := embedded)
      (a := fun _ => .inl true) 0 (by simp [embedded]))

/-- A concrete two-seed collision is detected by the single-seed condition II. -/
theorem embedded_empty_not_condII : ¬ CondII ternaryVariance [] embedded := by
  intro h
  have hS : Sol ternaryVariance [] (configSet ternaryVariance collisionAssignment) :=
    (sat_iff_sol _).mp (by simp [SatT])
  have hc := h (false, false, [1]) ⟨_, hS, collision_seeds.2⟩
    (false, true, [0]) (moves_reach embedded_return)
  exact hS.consistent (.pair false [0]) collision_seeds.1
    (cl_subset hS collision_seeds.2 hc)

/-- The characterization also rejects this example through II. -/
theorem embedded_collision_not_entails : ¬ ExistsEntailsT ternaryVariance [] embedded :=
  fun h => embedded_empty_not_condII
    ((three_conditions_mixed empty_sat embedded_sat).mp h).2.2

/-- Non-vacuity for both unsatisfiable-system branches of the characterization. -/
theorem contradictory_units {V : Type*} (v : V) :
    ¬ ∃ ρ, SatT ternaryVariance ρ [.bot v, .top v] := by
  rintro ⟨ρ, hρ⟩
  have hb : ρ v = DeciNSSE.Tree.bot := hρ (.bot v) (by simp)
  have ht : ρ v = DeciNSSE.Tree.top := hρ (.top v) (by simp)
  exact DeciNSSE.Tree.bot_ne_top (hb.symm.trans ht)

/-- An inconsistent antecedent entails every consequent. -/
theorem unsat_antecedent_entails :
    ExistsEntailsT ternaryVariance [.bot false, .top false] separate :=
  existsEntailsT_of_unsat (contradictory_units false)

/-- A satisfiable antecedent cannot entail an inconsistent consequent. -/
theorem unsat_consequent_not_entails : ¬ ExistsEntailsT ternaryVariance ([] : List (LitT 3 Bool))
    ([.bot (.inr ()), .top (.inr ())] : List (LitT 3 (Bool ⊕ Unit))) :=
  not_existsEntailsT_of_unsat empty_sat (contradictory_units (Sum.inr () : Bool ⊕ Unit))

/-- A satisfiable constructor system witnesses all three conditions at every arity. -/
theorem self_conditions (c : Fin n → Bool) :
    let φ : List (LitT n Unit) := [.lef () (fun _ => ())]
    let ψ : List (LitT n (Unit ⊕ Unit)) := [.lef (.inl ()) (fun _ => .inl ())]
    (∃ ρ, SatT c ρ φ) ∧ (∃ ρ, SatT c ρ ψ) ∧
      CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ := by
  dsimp
  have hφ : ∃ ρ, SatT c ρ [.lef () (fun _ => ())] :=
    ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT]⟩
  have hψ : ∃ ρ, SatT c ρ
      ([.lef (.inl ()) (fun _ => .inl ())] : List (LitT n (Unit ⊕ Unit))) :=
    ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT]⟩
  refine ⟨hφ, hψ, (three_conditions_mixed hφ hψ).mp ?_⟩
  intro ρ _ hρ
  refine ⟨fun _ => DeciNSSE.Tree.bot, fun _ => trivial, ?_⟩
  simpa [SatT, HoldsT, Function.comp_def] using hρ

/-- Binary arrow variance, with a constructor literal. -/
theorem binary_arrow_conditions :
    let c : Fin 2 → Bool := ![true, false]
    let φ : List (LitT 2 Unit) := [.lef () (fun _ => ())]
    let ψ : List (LitT 2 (Unit ⊕ Unit)) := [.lef (.inl ()) (fun _ => .inl ())]
    CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ :=
  (self_conditions ![true, false]).2.2

/-- The same interface needs no branching at unary contravariant variance. -/
theorem unary_conditions :
    let c : Fin 1 → Bool := fun _ => true
    let φ : List (LitT 1 Unit) := [.lef () (fun _ => ())]
    let ψ : List (LitT 1 (Unit ⊕ Unit)) := [.lef (.inl ()) (fun _ => .inl ())]
    CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ :=
  (self_conditions (n := 1) (fun _ => true)).2.2

/-- At arity zero the constructor still contributes its forbidden root. -/
theorem nullary_conditions (c : Fin 0 → Bool) :
    let φ : List (LitT 0 Unit) := [.lef () (fun _ => ())]
    let ψ : List (LitT 0 (Unit ⊕ Unit)) := [.lef (.inl ()) (fun _ => .inl ())]
    CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ :=
  (self_conditions c).2.2

end ConditionsExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words
open DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*}

namespace MembershipExamples
open LeafHornExamples

/-- Both parts of unit support have actual inhabitants. -/
theorem negative_unit : DeadT ternaryVariance ternaryLit (false, false) [] :=
  Or.inl (reach_neg_iff.mp DualityExamples.negative_root_witness)

/-- The forced positive unit makes every opposite seed dead. -/
theorem positive_unit (u : List (Fin 3)) :
    DeadT ternaryVariance DualityExamples.forced ((), false) u :=
  Or.inr ⟨[], by simpa using DualityExamples.forced_opposite u⟩

/-- The unsupported premise is inhabited in the no-joint-parity example. -/
theorem live_unsupported : ¬ DeadT ternaryVariance ternaryLit (false, false) [0] :=
  fun h => deadT_not_live h DualityExamples.mixed_zero_live

/-- An unsupported mixed prefix has empty later upper summaries. -/
theorem cone_example :
    Automata.P (signedSys ternaryVariance ternaryLit) (false, false) [0, 1] = ∅ := by
  exact cone (u := [0, 1]) (J := 1) (j := 2) live_unsupported (by decide) (by decide)

/-- A live seed belongs to its own singleton closure. -/
theorem live_membership :
    (false, false, [0]) ∈ Cl ternaryVariance ternaryLit (false, false, [0]) := by
  apply (cl_membership_live DualityExamples.mixed_zero_live).mpr
  refine Or.inr ⟨0, by decide, 0, by decide, List.prefix_refl _, ?_⟩
  refine ⟨(false, false), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
    simp only [List.take_zero, Automata.P_nil, Automata.Q_nil, Automata.mem_up, Automata.mem_down]
      <;>
    exact Automata.d_refl _ _

/-- A genuine self event, with no unit support, for x ≤ f(x,x,x). -/
theorem self_event : SelfEv ternaryVariance DualityExamples.self ((), false) [0] 0 1 := by
  refine ⟨by decide, by decide, List.nil_prefix, ?_⟩
  decide +kernel

/-- The self-return example is not unit dead. -/
theorem self_unsupported : ¬ DeadT ternaryVariance DualityExamples.self ((), false) [0] := by
  rw [deadT_iff_state]
  rintro (hn | hm | ⟨e, he, hh⟩)
  · have h : ¬ negReachS ternaryVariance DualityExamples.self
        (Automata.P (signedSys ternaryVariance DualityExamples.self) ((), false) [0]) := by
          decide +kernel
    exact h hn
  · have h : ¬ muReachS ternaryVariance DualityExamples.self
        (Automata.P (signedSys ternaryVariance DualityExamples.self) ((), false) [0]) := by
          decide +kernel
    exact h hm
  · have he' : e ≤ 1 := he
    interval_cases e <;> revert hh <;> decide +kernel

/-- The self-return example is dead through a self event. -/
theorem self_deadness : ¬ Live ternaryVariance DualityExamples.self ((), false, [0]) :=
  (dead_iff_unit_or_self (sat_iff_mu.mp DualityExamples.self_sat)).mpr
    (Or.inr ⟨0, 1, self_event⟩)

/-- A consequent upper constructor bound with a hidden child. -/
def headSystem : List (LitT 3 (Unit ⊕ Unit)) := [.lef (.inl ()) (fun _ => .inr ())]

/-- The head example has the required nonempty summary intersection. -/
theorem head_nonempty :
    (Automata.P (signedSys ternaryVariance headSystem) (.inl (), false) [1]).Nonempty := by
  refine ⟨(.inr (), false), (mem_P_iff_moves _).mpr
    ((moves_iff_signed (c := ternaryVariance) (χ := headSystem) (p := (.inl (), false, [1]))
      (q := (.inr (), false, []))).mp ?_)⟩
  apply Relation.ReflTransGen.single
  exact Move.lefPop (c := ternaryVariance) (χ := headSystem)
    (a := fun _ => Sum.inr ()) 1 (by simp [headSystem])

/-- The `head_prefix_deadU` conclusion applies to the concrete nonempty head. -/
theorem head_unit : DeadU ternaryVariance headSystem ((), false) [] :=
  head_prefix_deadU (i := 0) head_nonempty (by decide)

/-- The target reader starts in a unit target. -/
theorem reader_unit :
    (targetDFA ternaryVariance ([] : List (LitT 3 Unit)) headSystem ((), false)).run [] ∈
      targetUnit ternaryVariance [] headSystem := by
  apply (targetDFA_unit _ _).mpr
  refine ⟨?_, head_unit⟩
  intro hd
  apply deadT_not_live hd
  refine ⟨configSet ternaryVariance (fun _ => DeciNSSE.Tree.top),
    (sat_iff_sol _).mp (by simp [SatT]), ?_⟩
  simp [configSet]

/-- The third letter also creates a self event at the contravariant child. -/
theorem third_child_self_event :
    SelfEv ternaryVariance DualityExamples.self ((), false) [2] 0 1 := by
  refine ⟨by decide, by decide, List.nil_prefix, ?_⟩
  decide +kernel

/-- The shared reader and bounded support tests need no letter at arity zero. -/
theorem nullary_reader_rej :
    (targetDFA (n := 0) (fun _ => false) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))) ((), false)).run [] ∈
        targetRej (n := 0) (fun _ => false) [] [] := by
  decide +kernel

end MembershipExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self
open DeciENSSE.Core.Full
variable {n : ℕ}
variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

variable {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
variable (p : X × Bool)

/-- The raw first rejection ignores the consequent negative-unit enrichment. -/
def extractRawJ (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (p : X × Bool) (u : List (Fin n)) : Option ℕ :=
  (List.range (u.length + 1)).find? fun e =>
    decide (¬ targetDeadT c φ ((targetDFA c φ ψ p).atCut u e))


/-- The raw cut is the first prefix without antecedent unit deadness. -/
theorem extractRawJ_eq_some_iff (u : List (Fin n)) (j : ℕ) :
    extractRawJ c φ ψ p u = some j ↔
      ¬ DeadT c φ p (u.take j) ∧ j ≤ u.length ∧
        ∀ i < j, DeadT c φ p (u.take i) := by
  classical
  simp only [extractRawJ, List.find?_range_eq_some, Bool.not_eq_true_eq_eq_false,
    decide_eq_true_eq, decide_eq_false_iff_not, not_not, List.mem_range,
    Nat.lt_succ_iff, LDFA.atCut, targetDFA_deadT]


namespace ExtractExamples
open DeciNSSE

/-- The binary arrow variance for the raw-cut counterexample. -/
def arrow : Fin 2 → Bool := ![true, false]

/-- Visible false = x, true = y; hidden false = a, true = c. -/
def antecedent : List (LitT 2 Bool) := [.lef false ![false, false]]
/-- The consequent used to distinguish raw and enriched rejection cuts. -/
def consequent : List (LitT 2 (Bool ⊕ Bool)) :=
  [.lef (.inl false) ![.inr false, .inl false],
   .fle ![.inr true, .inl true] (.inr false)]

/-- A visible assignment separating antecedent and consequent. -/
def countermodel (v : Bool) : Tree 2 :=
  if v then DeciNSSE.Tree.top else
    DeciNSSE.Tree.node ![DeciNSSE.Tree.node ![DeciNSSE.Tree.bot, DeciNSSE.Tree.bot],
      DeciNSSE.Tree.bot]

/-- The separating assignment satisfies the antecedent. -/
theorem countermodel_sat : SatT arrow countermodel antecedent := by
  simp only [SatT, antecedent, List.mem_singleton, forall_eq, HoldsT, countermodel,
    Bool.false_eq_true, ↓reduceIte]
  apply (node_treeLe_node_iff _ _ _).mpr
  intro i
  fin_cases i <;> simp [countermodel, arrow, node_treeLe_node_iff, treeLe_refl]

/-- The counterexample antecedent is satisfiable. -/
theorem antecedent_sat : ∃ ρ, SatT arrow ρ antecedent := ⟨countermodel, countermodel_sat⟩

/-- The counterexample consequent is satisfiable. -/
theorem consequent_sat : ∃ ρ, SatT arrow ρ consequent := by
  refine ⟨Sum.elim (fun _ => DeciNSSE.Tree.bot) (fun _ => DeciNSSE.Tree.top), ?_⟩
  simp [SatT, HoldsT, consequent]

/-- For negative-unit avoidance only, consistency of this larger set is unnecessary. -/
def unitEnvelope (S : Set (Config 2 Bool)) : Set (Config 2 (Bool ⊕ Bool)) :=
  {a | match a.1, a.2.1 with
    | .inl false, false => (false, false, a.2.2) ∈ S
    | .inr false, true => (false, false, 0 :: a.2.2) ∈ S
    | _, _ => True}

/-- The unit envelope is clause closed. -/
theorem unitEnvelope_closed {S : Set (Config 2 Bool)} (hS : Sol arrow antecedent S) :
    Closed arrow consequent (unitEnvelope S) := by
  intro p q h hp
  cases h with
  | extend v s w i =>
    cases v with
    | inl v => cases v <;> cases s <;> simp only [unitEnvelope, Set.mem_ofPred_eq] at hp ⊢
               exact hS.closed (.extend _ _ _ _) hp
    | inr v => cases v <;> cases s <;> simp only [unitEnvelope, Set.mem_ofPred_eq] at hp ⊢
               exact hS.closed (.extend _ _ _ _) hp
  | move hm =>
    cases hm with
    | copyPlus hl => simp [consequent] at hl
    | copyMinus hl => simp [consequent] at hl
    | flePush i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
        reduceCtorEq, false_or, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i <;> trivial
    | flePop i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
        reduceCtorEq, false_or, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i <;> trivial
    | lefPush i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
        reduceCtorEq, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      trivial
    | lefPop i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
        reduceCtorEq, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i
      · exact hp
      · exact hS.closed (.move (.lefPop (a := ![false, false]) 1 (by simp [antecedent]))) hp

/-- The unit envelope avoids negative roots. -/
theorem unitEnvelope_avoids {S : Set (Config 2 Bool)} (hS : Sol arrow antecedent S) :
    Avoids consequent (unitEnvelope S) := by
  intro n hn hneg
  cases hneg with
  | lef hl =>
    simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
      reduceCtorEq, or_false] at hl
    rcases hl with ⟨rfl, rfl⟩
    exact hS.avoids hn (.lef (a := ![false, false]) (by simp [antecedent]))
  | fle hl =>
    simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
      reduceCtorEq, false_or, or_false] at hl
    rcases hl with ⟨rfl, rfl⟩
    have hm : (false, true, []) ∈ S :=
      hS.closed (.move (.lefPop (a := ![false, false]) 0 (by simp [antecedent]))) hn
    exact hS.consistent (.pair false [0]) hn (hS.closed (.extend _ _ _ 0) hm)

/-- The unit premise holds for the whole system, not merely the exhibited seed. -/
theorem condU : CondU arrow antecedent consequent := by
  rintro ⟨x, s, w⟩ ⟨S, hS, ha⟩ n hn hr
  have hseed : visible (Z := Bool) (x, s, w) ∈ unitEnvelope S := by
    cases x <;> cases s <;> simp_all [visible, unitEnvelope]
  exact unitEnvelope_avoids hS (hr.mem_of_closed (unitEnvelope_closed hS) hseed) hn

/-- The counterexample source atom is live. -/
theorem source_live : Live arrow antecedent (false, false, [0, 1]) := by
  refine ⟨configSet arrow countermodel, (sat_iff_sol _).mp countermodel_sat, ?_⟩
  simp [configSet, countermodel, arrow]

/-- The target atom is outside the source's antecedent closure. -/
theorem target_not_cl :
    (true, true, []) ∉ Cl arrow antecedent (false, false, [0, 1]) := by
  intro h
  have hm := cl_subset ((sat_iff_sol _).mp countermodel_sat)
    (show (false, false, [0, 1]) ∈ configSet arrow countermodel by
      simp [configSet, countermodel, arrow]) h
  simp [configSet, countermodel] at hm

/-- The consequent provides the required head path. -/
theorem head_moves :
    Moves arrow consequent (.inl false, false, [0, 1]) (.inl true, true, []) := by
  apply Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Move.lefPop (c := arrow) (χ := consequent)
      (a := ![.inr false, .inl false]) 0 (by simp [consequent])))
  exact Relation.ReflTransGen.single (Move.flePop (c := arrow) (χ := consequent)
    (a := ![.inr true, .inl true]) 1 (by simp [consequent]))

/-- The hole is witnessed by liveness and a concrete tree model, without powerset-state
enumeration. -/
theorem hole :
    (extractSelf arrow antecedent consequent (false, false) (true, true)).IsHole [] [0, 1] :=
  (extractSelf_isHoleS_iff _ _ antecedent_sat condU _ _).mpr
    ⟨source_live, head_moves, target_not_cl⟩

/-- The head upper summary is nonempty. -/
theorem head_upper_nonempty :
    (Automata.P (signedSys arrow consequent) (.inl false, false) [0, 1]).Nonempty := by
  exact ⟨(.inl true, true), (mem_P_iff_moves _).mpr (moves_iff_signed.mp head_moves)⟩

/-- All proper head prefixes, including the raw rejected cut, are in DeadU. -/
theorem head_prefix_supported (i : ℕ) (hi : i < 2) :
    DeadU arrow consequent (false, false) ([0, 1].take i) :=
  head_prefix_deadU head_upper_nonempty hi

/-- The raw reader supports the empty prefix. -/
theorem raw_root_supported : DeadT arrow antecedent (false, false) [] := by
  apply Or.inl
  apply reach_neg_iff.mp
  exact ⟨(false, false, []), .lef (a := ![false, false]) (by simp [antecedent]), .refl⟩

/-- The counterexample antecedent has no positive units. -/
theorem no_facts {a : Config 2 Bool} : ¬ Fact antecedent a := by
  intro h
  cases h <;> simp_all [antecedent]

/-- A closed, negative-unit-avoiding set containing x⁺(0), although inconsistent. -/
def rawEnvelope : Set (Config 2 Bool) :=
  {a | a.2.1 = true ∨ ∃ w, a.2.2 = 0 :: w}

/-- The raw envelope is clause closed. -/
theorem rawEnvelope_closed : Closed arrow antecedent rawEnvelope := by
  intro p q h hp
  cases h with
  | extend v s w i =>
    rcases hp with hs | ⟨v, rfl⟩
    · exact Or.inl hs
    · exact Or.inr ⟨v ++ [i], rfl⟩
  | move hm =>
    cases hm with
    | copyPlus hl => simp [antecedent] at hl
    | copyMinus hl => simp [antecedent] at hl
    | flePush i hl => simp [antecedent] at hl
    | flePop i hl => simp [antecedent] at hl
    | lefPush i hl => exact Or.inl rfl
    | lefPop i hl =>
      simp only [antecedent, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · simp [rawEnvelope] at hp

/-- The raw envelope avoids forbidden root atoms. -/
theorem rawEnvelope_avoids : Avoids antecedent rawEnvelope := by
  intro n hn hneg
  cases hneg with
  | fle hl => simp [antecedent] at hl
  | lef hl =>
    simp only [antecedent, List.mem_singleton, LitT.lef.injEq] at hl
    rcases hl with ⟨rfl, rfl⟩
    simp [rawEnvelope] at hn

/-- The one-letter prefix is unsupported in the raw reader. -/
theorem raw_one_unsupported : ¬ DeadT arrow antecedent (false, false) [0] := by
  rintro (hn | ⟨δ, hm⟩)
  · obtain ⟨n, hn, hr⟩ := reach_neg_iff.mpr hn
    exact rawEnvelope_avoids
      (hr.mem_of_closed rawEnvelope_closed (Or.inr ⟨[], rfl⟩)) hn
  · obtain ⟨a, ha, _⟩ := mem_mu.mp hm
    exact no_facts ha

/-- The raw first-rejection cut is one. -/
theorem rawJ_one : extractRawJ arrow antecedent consequent (false, false) [0, 1] = some 1 := by
  apply (extractRawJ_eq_some_iff _ _ _).mpr
  refine ⟨raw_one_unsupported, by decide, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  exact raw_root_supported

/-- The enriched first-rejection cut is two. -/
theorem enrichedJ_two :
    (extractSelf arrow antecedent consequent (false, false) (true, true)).J [0, 1] = some 2 := by
  apply (TwoWordInstance.J_eq_some_iff _ _ _).mpr
  refine ⟨?_, by decide, ?_⟩
  · apply (extractSelf_rej_iff _ _ _ _).mpr
    exact ⟨fun h => deadT_not_live h source_live,
      fun h => condU_iff.mp condU false false _ h source_live⟩
  · intro i hi hr
    exact ((extractSelf_rej_iff _ _ _ _).mp hr).2 (head_prefix_supported i hi)

/-- The head is after the raw cut and exactly at the enriched cut. -/
theorem head_at_two :
    (extractSelf arrow antecedent consequent (false, false) (true, true)).HeadEvent
      [] [0, 1] 0 2 := by
  obtain ⟨e, he, i, hi, hh⟩ :=
    (extractSelf_head (false, false) (true, true) [] [0, 1]).mpr head_moves
  have he0 : e = 0 := by simp at he; omega
  subst e
  have hi2 : i = 2 := by
    have hd := congrArg List.length hh.1.2.2
    simp only [List.drop_nil, List.length_nil, List.length_drop, List.length_cons] at hd
    simp at hi
    omega
  subst i
  exact hh

/-- The defined-cut hypothesis really is necessary, even under (U): the raw unit-unsupported
prefix has a reflexive overlap, but enriched J is undefined. -/
theorem event_premise_needed :
    ¬ DeadT arrow antecedent (false, false) [0] ∧
    (Automata.P (signedSys arrow antecedent) (false, false) [] ∩
      Automata.Q (signedSys arrow antecedent) (false, false) []).Nonempty ∧
    ¬ ∃ e i, (extractSelf arrow antecedent consequent (false, false) (false, false)).Event
      [0] [0] e i := by
  refine ⟨raw_one_unsupported, ?_, ?_⟩
  · refine ⟨(false, false), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
      simp only [Automata.P_nil, Automata.Q_nil, Automata.mem_up, Automata.mem_down] <;>
      exact Automata.d_refl _ _
  · rintro ⟨e, i, _, ⟨j, hj, _⟩, _⟩
    have hsome :
        ((extractSelf arrow antecedent consequent (false, false) (false, false)).J [0]).isSome =
          true := by
      rw [show (extractSelf arrow antecedent consequent (false, false) (false, false)).J [0] =
        some j from hj]
      rfl
    have hdead : DeadU arrow consequent (false, false) [0] := head_prefix_supported 1 (by decide)
    exact ((extractSelf_J_isSome _ _ _).mp hsome).2 hdead

/-- The example also inhabits (I0), so its failed test is precisely (II). -/
theorem condI0 : CondI0 arrow antecedent consequent := by
  intro b hb
  obtain ⟨a, ha, _⟩ := mem_mu.mp hb
  cases ha <;> simp_all [consequent]

/-- The counterexample violates the singleton closure condition. -/
theorem not_condII : ¬ CondII arrow antecedent consequent := by
  intro h
  exact (condII_iff_no_holes antecedent_sat condU).mp h
    (false, false) (true, true) ⟨[], [0, 1], hole⟩

/-- The counterexample fails existential entailment. -/
theorem not_entails : ¬ ExistsEntailsT arrow antecedent consequent := by
  intro h
  exact not_condII (condII_of_existsEntailsT h)

/-- A third-child witness for the semantic hole equivalence and its premises. -/
def ternaryConsequent : List (LitT 3 (Bool ⊕ Unit)) :=
  [.le (.inl false) (.inl true)]

/-- The ternary example satisfies the unit condition. -/
theorem ternary_condU : CondU LeafHornExamples.ternaryVariance [] ternaryConsequent := by
  intro a ha b hb
  cases hb <;> simp_all [ternaryConsequent]

/-- Both systems in the ternary example are satisfiable. -/
theorem ternary_satisfiable :
    (∃ ρ : Bool → Tree 3, SatT LeafHornExamples.ternaryVariance ρ []) ∧
    (∃ ρ, SatT LeafHornExamples.ternaryVariance ρ ternaryConsequent) := by
  constructor
  · exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT]⟩
  · exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, ternaryConsequent, treeLe_refl]⟩

/-- The ternary extracted instance has a concrete hole. -/
theorem ternary_hole :
    (extractSelf LeafHornExamples.ternaryVariance [] ternaryConsequent
      (false, false) (true, false)).IsHole [2] [2] := by
  let ρ : Bool → Tree 3 := fun v => if v then DeciNSSE.Tree.bot else DeciNSSE.Tree.top
  have hs : Sol LeafHornExamples.ternaryVariance [] (configSet LeafHornExamples.ternaryVariance ρ)
    :=
    (sat_iff_sol _).mp (by simp [SatT])
  have hp : (false, false, [2]) ∈ configSet LeafHornExamples.ternaryVariance ρ := by
    simp [configSet, ρ]
  apply (extractSelf_isHoleS_iff _ _ ternary_satisfiable.1 ternary_condU _ _).mpr
  refine ⟨⟨_, hs, hp⟩, Relation.ReflTransGen.single (.copyPlus (by simp [ternaryConsequent])), ?_⟩
  intro h
  have hq := cl_subset hs hp h
  simp [configSet, ρ] at hq

/-- The ternary extraction has ForcedHeads and an actual hole. -/
theorem ternary_hypotheses :
    (extractSelf LeafHornExamples.ternaryVariance [] ternaryConsequent (false, false) (true,
      false)).ForcedHeads ∧
    (extractSelf LeafHornExamples.ternaryVariance [] ternaryConsequent (false, false) (true,
      false)).HasHole :=
  ⟨extractSelf_forcedHeads _ _, [2], [2], ternary_hole⟩

/-- The empty alphabet still has a defined first rejection, at its only cut. -/
theorem nullary_J :
    (extractSelf (n := 0) (fun _ => false) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))) ((), false) ((), false)).J [] = some 0 := by
  apply (TwoWordInstance.J_eq_some_iff _ _ _).mpr
  exact ⟨MembershipExamples.nullary_reader_rej, by decide, by omega⟩

/-- ForcedHeads also specializes at arity zero without an inhabitant of the alphabet. -/
theorem nullary_forcedHeads :
    (extractSelf (n := 0) (fun _ => false) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))) ((), false) ((), false)).ForcedHeads :=
  extractSelf_forcedHeads _ _

end ExtractExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words

variable {n : ℕ}
open DeciENSSE.Core.Full

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

namespace CondI0Examples
open LeafHornExamples

/-- The successful condition already has a mixed, nonempty consequent. -/
theorem mixed_positive :
    @decide (CondI0 ternaryVariance [] ConditionsExamples.separate)
      (decideCondI0 ternaryVariance [] ConditionsExamples.separate) = true :=
  (decideCondI0_true_iff _ _ _).mpr ConditionsExamples.separate_condI0

/-- A consequent forcing a visible positive root unit. -/
def forcedVisible : List (LitT 3 (Unit ⊕ Empty)) := [.top (.inl ())]

/-- A new visible positive unit witnesses failure at cut zero. -/
theorem forced_failure : FailureI0 ternaryVariance [] forcedVisible ((), false) [] := by
  apply (failureI0_iff _ _ _ _ _).mpr
  constructor
  · exact mem_mu.mpr ⟨(.inl (), false, []), .top (by simp [forcedVisible]), .refl⟩
  · intro hm
    obtain ⟨f, hf, _⟩ := mem_mu.mp hm
    cases hf <;> simp_all

/-- The positive-unit decision rejects an unforced visible consequent unit. -/
theorem forced_negative :
    @decide (CondI0 ternaryVariance [] forcedVisible) (decideCondI0 ternaryVariance []
      forcedVisible) = false := by
  rw [decide_eq_false_iff_not, not_condI0_iff]
  exact ⟨((), false), [], forced_failure⟩

/-- A forced visible root hit persists along the third child. -/
theorem third_child_failure : FailureI0 ternaryVariance [] forcedVisible ((), false) [2] := by
  decide +kernel

/-- There are no visible atoms when X is empty, even if ψ forces hidden facts. -/
theorem no_visible (c : Fin n → Bool) (ψ : List (LitT n (Empty ⊕ Unit))) :
    @decide (CondI0 c [] ψ) (decideCondI0 c [] ψ) = true := by
  rw [decideCondI0_true_iff]
  intro a
  exact a.1.elim

/-- Empty visible variables and an empty alphabet still admit the decision. -/
theorem nullary_no_visible :
    @decide (CondI0 (fun i : Fin 0 => i.elim0) []
      ([.top (.inr ())] : List (LitT 0 (Empty ⊕ Unit))))
      (decideCondI0 (fun i : Fin 0 => i.elim0) [] [.top (.inr ())]) = true :=
  no_visible _ _

end CondI0Examples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words

variable {n : ℕ}
open DeciENSSE.Core.Full DeciNSSE.Holes DeciNSSE.RejectedTail

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

namespace UnitsExamples
open LeafHornExamples MembershipExamples

/-- The semantic premise of the decision procedure is inhabited. -/
theorem empty_sat (c : Fin n → Bool) :
    ∃ ρ : Unit → DeciNSSE.Tree n, SatT c ρ [] :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT]⟩

/-- A real unit hole at epsilon, using the shared-reader example. -/
theorem epsilon_hole :
    IsReaderHole (unitReader ternaryVariance ([] : List (LitT 3 Unit)) headSystem ((), false))
      unitRelation (unitTarget ternaryVariance [] headSystem) [] := by
  apply (unit_empty_hole_iff ternaryVariance [] headSystem ((), false)).mpr
  exact reader_unit

/-- The epsilon hole witnesses failure of the unit condition. -/
theorem failed_unit_condition : ¬ CondU ternaryVariance ([] : List (LitT 3 Unit)) headSystem := by
  intro h
  exact (condU_iff_no_unit_holes ternaryVariance [] headSystem (empty_sat ternaryVariance)).mp h
    ((),false) [] epsilon_hole

/-- The unit decision rejects the epsilon-hole example. -/
theorem failed_decision :
    @decide (CondU ternaryVariance ([] : List (LitT 3 Unit)) headSystem)
      (decideCondU ternaryVariance [] headSystem (empty_sat ternaryVariance)) = false := by
  let := decideCondU ternaryVariance [] headSystem (empty_sat ternaryVariance)
  exact decide_eq_false failed_unit_condition

/-- The other branch is inhabited as well; empty consequents have no negative units. -/
theorem empty_condition :
    CondU ternaryVariance ([] : List (LitT 3 Unit)) ([] : List (LitT 3 (Unit ⊕ Unit))) := by
  intro _ _ _ hn
  cases hn <;> simp_all

/-- The unit decision accepts empty systems. -/
theorem successful_decision :
    @decide (CondU ternaryVariance ([] : List (LitT 3 Unit)) ([] : List (LitT 3 (Unit ⊕ Unit))))
      (decideCondU ternaryVariance [] [] (empty_sat ternaryVariance)) = true :=
  (decideCondU_correct ternaryVariance [] [] (empty_sat ternaryVariance)).mpr empty_condition

/-- A nullary upper constructor still forbids the positive root leaf. -/
def nullaryHead : List (LitT 0 (Unit ⊕ Unit)) := [.lef (.inl ()) Fin.elim0]

/-- The empty alphabet can have a real unit hole at epsilon. -/
theorem nullary_epsilon_hole :
    IsReaderHole (unitReader (fun i : Fin 0 => i.elim0) [] nullaryHead ((), false))
      unitRelation (unitTarget (fun i : Fin 0 => i.elim0) [] nullaryHead) [] := by
  apply (unit_empty_hole_iff _ _ _ _).mpr
  decide +kernel

/-- The generic unit decider is available at zero arity and detects this hole. -/
theorem nullary_failed_decision :
    @decide (CondU (fun i : Fin 0 => i.elim0) [] nullaryHead)
      (decideCondU _ [] nullaryHead (empty_sat _)) = false := by
  rw [decide_eq_false_iff_not]
  intro h
  exact (condU_iff_no_unit_holes _ [] nullaryHead (empty_sat _)).mp h
    ((), false) [] nullary_epsilon_hole

/-- At zero arity an empty consequent also supplies the successful branch. -/
theorem nullary_successful_decision :
    @decide (CondU (fun i : Fin 0 => i.elim0) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))))
      (decideCondU _ [] [] (empty_sat _)) = true := by
  apply (decideCondU_correct _ _ _ _).mpr
  intro _ _ _ hn
  cases hn <;> simp_all

end UnitsExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Full

namespace DecideMixedExamples
open LeafHornExamples ConditionsExamples

/-- A positive mixed input with no joint parity, for every candidate bound. Semantic correctness
avoids evaluating the enormous condition searches. -/
theorem mixed_positive (B : HoleBound) :
    (¬ ∃ s : Bool ⊕ Unit → Bool,
      ∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) ∧
    boundedCheckMixed B ternaryVariance ternaryLit embedded = true :=
  ⟨embedded_no_joint_parity, (boundedCheckMixed_eq_true B ternaryVariance ternaryLit embedded).mpr
    (boundedEntailsMixed_of_entails B embedded_entails)⟩

/-- The same consequent fails for the empty antecedent, without joint parity. -/
theorem mixed_negative (B : HoleBound) (hB : ShortHoleBoundSelf (Fin 3) B) :
    (¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) ∧
    boundedCheckMixed B ternaryVariance [] embedded = false := by
  refine ⟨embedded_empty_no_joint_parity, Bool.eq_false_iff.mpr ?_⟩
  intro h
  exact embedded_empty_not_entails
    ((existsEntails_iff_boundedCheckMixed B hB ternaryVariance [] embedded).mpr h)

/-- An explicit length-two signed hole, independent of a universal bound. -/
theorem extracted_bounded_hole :
    (extractSelf ExtractExamples.arrow ExtractExamples.antecedent ExtractExamples.consequent
      (false, false) (true, true)).BoundedHole 2 :=
  (SelfTwoWordInstance.boundedHole_iff _ _).mpr
    ⟨[], [0, 1], ExtractExamples.hole, by decide⟩

/-- The negative mixed example has a bounded extracted counterexample. -/
theorem extracted_bounded_false :
    boundedCheckMixed (fun _ _ _ _ => 2) ExtractExamples.arrow
      ExtractExamples.antecedent ExtractExamples.consequent = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rcases (boundedCheckMixed_eq_true _ _ _ _).mp h with hn | ⟨_, _, _, hh⟩
  · exact hn ExtractExamples.antecedent_sat
  · exact hh (false, false) (true, true) extracted_bounded_hole

/-- Kernel evaluation of the transported search, including a nonempty self guard. -/
theorem transported_search_positive :
    @decide (SelfTwoWordInstanceExamples.pending.BoundedHole 4)
      (SelfTwoWordInstance.decideBoundedHole SelfTwoWordInstanceExamples.pending 4) = true := by
  decide +kernel

/-- The unique underlying TwoWordInstance hole is removed by its strict target self event. -/
theorem transported_search_negative :
    @decide (SelfTwoWordInstanceExamples.uniqueBlocked.BoundedHole 1)
      (SelfTwoWordInstance.decideBoundedHole SelfTwoWordInstanceExamples.uniqueBlocked 1) = false
        := by
  decide +kernel

/-- A concrete extracted hole witnesses the short-bound hypotheses. -/
theorem short_hypotheses_nonvacuous :
    SelfTwoWordInstanceExamples.pending.ForcedHeads ∧ SelfTwoWordInstanceExamples.pending.HasHole :=
  ⟨SelfTwoWordInstanceExamples.pending_hypotheses.1,
    SelfTwoWordInstanceExamples.pending_hypotheses.2.1⟩
end DecideMixedExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

namespace FinalMixedExamples
open LeafHornExamples ConditionsExamples

/-- The bounded check accepts an input without joint parity. -/
theorem mixed_positive :
    (¬ ∃ s : Bool ⊕ Unit → Bool,
      ∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) ∧
    boundedCheckMixed selfHoleBound ternaryVariance ternaryLit embedded = true :=
  DecideMixedExamples.mixed_positive selfHoleBound

/-- The bounded check rejects an input without joint parity. -/
theorem mixed_negative :
    (¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) ∧
    boundedCheckMixed selfHoleBound ternaryVariance [] embedded = false :=
  DecideMixedExamples.mixed_negative selfHoleBound (shortHoleBoundSelf (Fin 3))

/-- The final decision accepts the mixed example without joint parity. -/
theorem decision_positive :
    @decide (ExistsEntailsT ternaryVariance ternaryLit embedded)
      (decideExistsEntails ternaryVariance ternaryLit embedded) = true :=
  (decideExistsEntails_correct ternaryVariance ternaryLit embedded).mpr embedded_entails

/-- The final decision rejects its empty-antecedent variant. -/
theorem decision_negative :
    @decide (ExistsEntailsT ternaryVariance [] embedded)
      (decideExistsEntails ternaryVariance [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact embedded_empty_not_entails ((decideExistsEntails_correct ternaryVariance [] embedded).mp h)

/-- The universal short-hole premise is proved, and has an actual ForcedHeads hole. -/
theorem bound_nonvacuous : ShortHoleBoundSelf (Fin 3) selfHoleBound ∧
    NonMortalExamples.ternaryPending.ForcedHeads ∧ NonMortalExamples.ternaryPending.HasHole :=
  ⟨shortHoleBoundSelf (Fin 3), NonMortalExamples.ternaryPending_forcedHeads,
    [1, 2], [1, 2], NonMortalExamples.ternary_pending_completion⟩

/-- A unary contravariant constructor system passes the final decision. -/
theorem unary_positive :
    @decide (ExistsEntailsT (fun _ : Fin 1 => true)
      [.lef () (fun _ => ())]
      ([.lef (.inl ()) (fun _ => .inl ())] : List (LitT 1 (Unit ⊕ Unit))))
      (decideExistsEntails _ _ _) = true := by
  apply (decideExistsEntails_correct _ _ _).mpr
  intro ρ _ hρ
  refine ⟨fun _ => DeciNSSE.Tree.bot, fun _ => trivial, ?_⟩
  simpa [SatT, HoldsT, Function.comp_def] using hρ

/-- Both outcomes of the nullary enumeration transfer to the general endpoint. -/
theorem nullary_positive :
    @decide (ExistsEntailsT Fin.elim0 [.bot 0, .top 1]
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit))))
      (decideExistsEntails _ _ _) = true := by
  rw [decideExistsEntails_nullary_agrees]
  decide +kernel

/-- The general decision rejects the displayed nullary non-entailment. -/
theorem nullary_negative :
    @decide (ExistsEntailsT Fin.elim0 [] ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit))))
      (decideExistsEntails _ _ _) = false := by
  rw [decideExistsEntails_nullary_agrees]
  decide +kernel

/-- A ternary bounded search, with a nonempty target self guard. -/
theorem ternary_search_positive :
    @decide (NonMortalExamples.ternaryPending.BoundedHole 4)
      (SelfTwoWordInstance.decideBoundedHole NonMortalExamples.ternaryPending 4) = true := by
  decide +kernel

/-- Empty alphabets still admit the pair of empty words and a nonempty self guard. -/
theorem nullary_search_positive :
    @decide (BoundExamples.emptyInstance.BoundedHole 0)
      (SelfTwoWordInstance.decideBoundedHole BoundExamples.emptyInstance 0) = true := by
  decide +kernel

end FinalMixedExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

namespace RegularMixedExamples
open LeafHornExamples ConditionsExamples

/-- Every transfer obligation holds for a satisfiable ternary system. -/
theorem transfer_nonvacuous :
    SatisfiableIn RegularTop ternaryVariance ternaryLit ∧
    BoundRealization RegularTop ternaryVariance ternaryLit ∧
    TwoObservationRealization RegularTop ternaryVariance ternaryLit ∧
    ClassExtension RegularTop ternaryVariance embedded :=
  ⟨satisfiable_regular ternaryVariance DualityExamples.mixed_sat,
    regular_bound_realization ternaryVariance ternaryLit,
    (regular_bound_realization ternaryVariance ternaryLit).observations,
    regular_class_extension ternaryVariance embedded⟩

/-- The decision procedure returns true on the ternary entailment example. -/
theorem ternary_positive :
    @decide _ (decideExistsEntailsReg ternaryVariance ternaryLit embedded) = true :=
  (decideExistsEntailsReg_correct _ _ _).mpr
    ((existsEntailsTReg_iff_mixed _ _ _).mpr embedded_entails)

/-- The decision procedure returns false on the ternary entailment example. -/
theorem ternary_negative :
    @decide _ (decideExistsEntailsReg ternaryVariance [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact embedded_empty_not_entails ((existsEntailsTReg_iff_mixed _ _ _).mp
    ((decideExistsEntailsReg_correct _ _ _).mp h))

/-- The contravariant unary fixed point has regular hidden witnesses. -/
theorem unary_positive :
    @decide _ (decideExistsEntailsReg (fun _ => true) []
      ([.lef (.inr ()) (fun _ => .inr ()), .fle (fun _ => .inr ()) (.inr ())] :
        List (LitT 1 (Unit ⊕ Unit)))) = true := by
  apply (decideExistsEntailsReg_correct _ _ _).mpr
  intro ρ _
  refine ⟨fun _ => RGraph.allF 1, ?_⟩
  have h := RGraph.allF_unfold_node (n := 1)
  simp [SatT, HoldsT, Function.comp_def, ← h, DeciNSSE.treeLe_refl]

/-- The decision procedure returns true on the nullary entailment example. -/
theorem nullary_positive :
    @decide _ (decideExistsEntailsReg Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = true  := by
  rw [Subsingleton.elim (decideExistsEntailsReg (X := Fin 2) (Z := Unit) Fin.elim0 _ _)
    (Nullary.decideExistsEntailsReg _ _ _)]
  decide +kernel

/-- The decision procedure returns false on the nullary entailment example. -/
theorem nullary_negative :
    @decide _ (decideExistsEntailsReg Fin.elim0 []
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = false  := by
  rw [Subsingleton.elim (decideExistsEntailsReg (X := Fin 2) (Z := Unit) Fin.elim0 _ _)
    (Nullary.decideExistsEntailsReg _ _ _)]
  decide +kernel

end RegularMixedExamples

end DeciENSSE.Core.Mixed

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words DeciENSSE.Core.Words.Self DeciENSSE.Core.Words.Mortal
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

namespace FiniteMixedExamples
open LeafHornExamples ConditionsExamples

/-- The mixed-variance example has a finite solution. -/
theorem mixed_finite : SatFin ternaryVariance ternaryLit :=
  ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩,
    by simp [SatT, HoldsT, ternaryLit]⟩

/-- The embedded example has a finite solution. -/
theorem embedded_finite : SatFin ternaryVariance embedded :=
  ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩,
    by simp [SatT, HoldsT, embedded]⟩

/-- Finite transfer premises hold with an actual finite solution. -/
theorem transfer_nonvacuous :
    SatFin ternaryVariance ternaryLit ∧ BoundRealization FiniteTop ternaryVariance ternaryLit ∧
    TwoObservationRealization FiniteTop ternaryVariance ternaryLit ∧
    ClassExtension FiniteTop ternaryVariance embedded :=
  ⟨mixed_finite, finite_bound_realization ternaryVariance ternaryLit mixed_finite,
    (finite_bound_realization ternaryVariance ternaryLit mixed_finite).observations,
    finite_class_extension embedded_finite⟩

/-- The same no-joint-parity ternary example in all three tree classes. -/
theorem ternary_all_classes :
    ExistsEntailsT ternaryVariance ternaryLit embedded ∧
    ExistsEntailsTReg ternaryVariance ternaryLit embedded ∧ ExistsEntailsTFin ternaryVariance
      ternaryLit embedded :=
  ⟨embedded_entails, (existsEntailsTReg_iff_mixed _ _ _).mpr embedded_entails,
    (existsEntailsTFin_iff_mixed _ _ _).mpr (Or.inr ⟨embedded_finite, embedded_entails⟩)⟩

/-- The ternary example has no common parity assignment for both constraint systems. -/
theorem ternary_no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (ternaryVariance i)) :=
  embedded_no_joint_parity

/-- The decision procedure returns true on the ternary entailment example. -/
theorem ternary_positive :
    @decide _ (decideExistsEntailsFin ternaryVariance ternaryLit embedded) = true :=
  (decideExistsEntailsFin_correct _ _ _).mpr ternary_all_classes.2.2

/-- The decision procedure returns false on the ternary entailment example. -/
theorem ternary_negative :
    @decide _ (decideExistsEntailsFin ternaryVariance [] embedded) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (existsEntailsTFin_iff_mixed _ _ _).mp
    ((decideExistsEntailsFin_correct _ _ _).mp h)
  rcases he with hn | ⟨_, he⟩
  · exact hn ⟨fun _ => DeciNSSE.Tree.bot, fun _ => ⟨FTree.bot, rfl⟩, by simp [SatT]⟩
  · exact embedded_empty_not_entails he

/-- The same unary fixed point is rejected over finite trees. -/
theorem unary_negative :
    @decide _ (decideExistsEntailsFin (fun _ => true) []
      ([.lef (.inr ()) (fun _ => .inr ()), .fle (fun _ => .inr ()) (.inr ())] :
        List (LitT 1 (Unit ⊕ Unit)))) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (decideExistsEntailsFin_correct _ _ _).mp h
  obtain ⟨σ, hs⟩ := he (fun _ => FTree.bot) (by simp [SatT])
  have hlo := hs (.lef (.inr ()) (fun _ => .inr ())) (by simp)
  have hhi := hs (.fle (fun _ => .inr ()) (.inr ())) (by simp)
  have hfix : σ () = FTree.node (fun _ => σ ()) :=
    FTree.toTree_injective (DeciNSSE.treeLe_antisymm hlo hhi)
  have hh := FTree.height_child_lt (fun _ : Fin 1 => σ ()) 0
  rw [← hfix] at hh
  exact (Nat.lt_irrefl _ hh)

/-- The decision procedure returns true on the nullary entailment example. -/
theorem nullary_positive :
    @decide _ (decideExistsEntailsFin Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = true  := by
  rw [Subsingleton.elim (decideExistsEntailsFin (X := Fin 2) (Z := Unit) Fin.elim0 _ _)
    (Nullary.decideExistsEntailsFin _ _ _)]
  decide +kernel

/-- The decision procedure returns false on the nullary entailment example. -/
theorem nullary_negative :
    @decide _ (decideExistsEntailsFin Fin.elim0 []
      ([.le (.inl 0) (.inr ()), .le (.inr ()) (.inl 1),
        .fle Fin.elim0 (.inr ()), .lef (.inr ()) Fin.elim0,
        .bot (.inl 0), .top (.inl 1)] : List (LitT 0 (Fin 2 ⊕ Unit)))) = false  := by
  rw [Subsingleton.elim (decideExistsEntailsFin (X := Fin 2) (Z := Unit) Fin.elim0 _ _)
    (Nullary.decideExistsEntailsFin _ _ _)]
  decide +kernel

/-- Finite satisfiability is true on the nullary example. -/
theorem nullary_sat_positive :
    @decide _ (decideSatFin Fin.elim0
      ([.bot 0, .top 1] : List (LitT 0 (Fin 2)))) = true := by decide +kernel

/-- Finite satisfiability is false on the nullary example. -/
theorem nullary_sat_negative :
    @decide _ (decideSatFin Fin.elim0 [.bot (), .top ()]) = false := by decide +kernel

/-- Finite satisfiability is true on the ternary example. -/
theorem ternary_sat_positive :
    @decide _ (decideSatFin ternaryVariance ternaryLit) = true :=
  (decideSatFin_correct _ _).mpr mixed_finite

end FiniteMixedExamples

end DeciENSSE.Core.Mixed
