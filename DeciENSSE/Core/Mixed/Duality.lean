import DeciENSSE.Core.Mixed.LeafHorn

/-! # Duality and singleton deadness for leaf Horn presentations

Pure moves reverse under sign flip. Singleton liveness and deadness reduce
to the least closure, negative units, and collisions at every arity.

## Main declarations

- `Moves`, `flipC`, `move_dual`, `moves_dual`,
  `moves_append`, `reach_iff_moves`, `Mu`, `Cl`, `Live`, `live_iff`,
  `sat_iff_mu`, `collision_return`, `dead_iff`.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {χ : List (LitT n V)}

/-- Pure paths, without structural right extensions. -/
abbrev Moves (c : Fin n → Bool) (χ : List (LitT n V)) :=
  Relation.ReflTransGen (Move c χ)

/-- The opposite leaf atom, not the Boolean complement of membership. -/
def flipC (p : Config n V) : Config n V := (p.1, !p.2.1, p.2.2)

/-- Flipping a configuration twice is the identity. -/
@[simp] theorem flipC_flipC (p : Config n V) : flipC (flipC p) = p := by
  simp [flipC]

/-- The six literal moves occur in opposite-sign reverse pairs. -/
theorem move_dual {p q : Config n V} (h : Move c χ p q) :
    Move c χ (flipC q) (flipC p) := by
  cases h with
  | copyPlus hl => exact .copyMinus hl
  | copyMinus hl => exact .copyPlus hl
  | flePush i hl => exact .flePop i hl
  | flePop i hl => simpa [flipC] using Move.flePush (c := c) i hl
  | lefPop i hl => exact .lefPush i hl
  | lefPush i hl => simpa [flipC] using Move.lefPop (c := c) i hl

/-- Reverse a pure path and flip every sign. -/
theorem moves_dual {p q : Config n V} (h : Moves c χ p q) :
    Moves c χ (flipC q) (flipC p) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.head (move_dual hm)

/-- A literal move preserves a common right suffix. -/
theorem move_append (σ : List (Fin n)) {p q : Config n V} (h : Move c χ p q) :
    Move c χ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  cases h with
  | copyPlus hl => exact .copyPlus hl
  | copyMinus hl => exact .copyMinus hl
  | flePush i hl => exact .flePush i hl
  | flePop i hl => exact .flePop i hl
  | lefPop i hl => exact .lefPop i hl
  | lefPush i hl => exact .lefPush i hl

/-- Every pure move touches only the head of the word. -/
theorem moves_append (σ : List (Fin n)) {p q : Config n V} (h : Moves c χ p q) :
    Moves c χ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail (move_append σ hm)

/-- Compose two finite derivations. -/
theorem Reach.trans {a b d : Config n V} (hab : Reach c χ a b)
    (hbd : Reach c χ b d) : Reach c χ a d := by
  induction hbd with
  | refl => exact hab
  | step _ hs ih => exact .step ih hs

/-- Pure literal paths are clause derivations. -/
theorem moves_reach {a b : Config n V} (h : Moves c χ a b) : Reach c χ a b := by
  induction h with
  | refl => exact .refl
  | tail _ hm ih => exact .step ih (.move hm)

/-- Any right extension is reachable. -/
theorem reach_extend (v : V) (s : Bool) (u α : List (Fin n)) :
    Reach c χ (v, s, u) (v, s, u ++ α) := by
  induction α using List.reverseRecOn with
  | nil => simpa using (Reach.refl : Reach c χ (v, s, u) (v, s, u))
  | append_singleton α i ih =>
    simpa [List.append_assoc] using Reach.step ih (.extend v s (u ++ α) i)

/-- Commute every structural extension to the beginning of a path. -/
theorem reach_iff_moves {v : V} {s : Bool} {u : List (Fin n)} {b : Config n V} :
    Reach c χ (v, s, u) b ↔ ∃ α, Moves c χ (v, s, u ++ α) b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], by simpa using (Relation.ReflTransGen.refl)⟩
    | step _ hs ih =>
      obtain ⟨α, hα⟩ := ih
      cases hs with
      | move hm => exact ⟨α, hα.tail hm⟩
      | extend v' s' w i =>
        exact ⟨α ++ [i], by simpa [List.append_assoc] using moves_append [i] hα⟩
  · rintro ⟨α, hα⟩
    exact (reach_extend v s u α).trans (moves_reach hα)

/-- The positive closure of the units. -/
def Mu (c : Fin n → Bool) (χ : List (LitT n V)) : Set (Config n V) := Hull c χ ∅

/-- The positive closure of the units and one seed. -/
def Cl (c : Fin n → Bool) (χ : List (LitT n V)) (a : Config n V) : Set (Config n V) :=
  Hull c χ {a}

/-- Semantic singleton liveness. -/
def Live (c : Fin n → Bool) (χ : List (LitT n V)) (a : Config n V) : Prop :=
  ∃ S, Sol c χ S ∧ a ∈ S

/-- Unit closure is reachability from a positive root unit. -/
theorem mem_mu {b : Config n V} :
    b ∈ Mu c χ ↔ ∃ a, Fact χ a ∧ Reach c χ a b := by
  simp [Mu, Hull]

/-- A singleton closure consists of unit closure and reachable atoms. -/
theorem mem_cl {a b : Config n V} :
    b ∈ Cl c χ a ↔ b ∈ Mu c χ ∨ Reach c χ a b := by
  simp [Cl, Mu, Hull, or_and_right, exists_or]

/-- Every solution contains unit closure. -/
theorem mu_subset {S : Set (Config n V)} (hS : Sol c χ S) : Mu c χ ⊆ S :=
  hull_least hS.closed hS.facts (Set.empty_subset _)

/-- Every solution containing a seed contains its singleton closure. -/
theorem cl_subset {S : Set (Config n V)} {a : Config n V}
    (hS : Sol c χ S) (ha : a ∈ S) : Cl c χ a ⊆ S :=
  hull_least hS.closed hS.facts (Set.singleton_subset_iff.mpr ha)

/-- No satisfiability assumption is needed for this least-model test. -/
theorem live_iff {a : Config n V} :
    Live c χ a ↔ Avoids χ (Cl c χ a) ∧ Consistent (Cl c χ a) := by
  constructor
  · rintro ⟨S, hS, ha⟩
    have hsub := cl_subset hS ha
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    exact ⟨Cl c χ a, ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩,
      subset_hull _ (Set.mem_singleton a)⟩

/-- Satisfiability is avoidance and consistency of unit closure. -/
theorem sat_iff_mu :
    (∃ ρ, SatT c ρ χ) ↔ Avoids χ (Mu c χ) ∧ Consistent (Mu c χ) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have hS := (sat_iff_sol ρ).mp hρ
    have hsub := mu_subset hS
    exact ⟨fun {_} hp => hS.avoids (hsub hp),
      fun {_ _} h hp hq => hS.consistent h (hsub hp) (hsub hq)⟩
  · rintro ⟨hn, hd⟩
    obtain ⟨ρ, hρ, _⟩ := sol_iff_assignment.mp
      (show Sol c χ (Mu c χ) from
        ⟨hull_closed _, (fun {_} => hull_facts _), hn, hd⟩)
    exact ⟨ρ, hρ⟩

/-- Liveness persists under right extensions. -/
theorem live_extend {v : V} {s : Bool} {u : List (Fin n)} (α : List (Fin n))
    (h : Live c χ (v, s, u)) : Live c χ (v, s, u ++ α) := by
  obtain ⟨S, hS, ha⟩ := h
  exact ⟨S, hS, (reach_extend v s u α).mem_of_closed hS.closed ha⟩

/-- Extending a seed can only shrink its closure. -/
theorem cl_extend_subset (v : V) (s : Bool) (u α : List (Fin n)) :
    Cl c χ (v, s, u ++ α) ⊆ Cl c χ (v, s, u) := by
  apply hull_least (hull_closed _) (fun {_} => hull_facts _)
  exact Set.singleton_subset_iff.mpr (mem_cl.mpr (Or.inr (reach_extend v s u α)))

/-- Reverse the second collision branch after moving its extensions to its seed. -/
theorem collision_return {a : Config n V} {h q : V} {s s' : Bool} {w v : List (Fin n)}
    (h₁ : Reach c χ a (h, s, w)) (h₂ : Reach c χ (q, s', v) (h, !s, w)) :
    ∃ δ, Reach c χ a (q, !s', v ++ δ) := by
  obtain ⟨δ, hd⟩ := reach_iff_moves.mp h₂
  refine ⟨δ, h₁.trans (moves_reach ?_)⟩
  simpa [flipC] using moves_dual hd

/-- Exclusion with either choice of the first sign. -/
theorem Consistent.not_flip {S : Set (Config n V)} (hc : Consistent S)
    {v : V} {s : Bool} {w : List (Fin n)} (hp : (v, s, w) ∈ S) : (v, !s, w) ∉ S := by
  intro hm
  cases s with
  | false => exact hc (.pair v w) hp hm
  | true => exact hc (.pair v w) hm hp

/-- The three and only three causes of singleton deadness in a satisfiable system. -/
theorem dead_iff (hsat : Avoids χ (Mu c χ) ∧ Consistent (Mu c χ))
    {p : V} {s : Bool} {u : List (Fin n)} :
    ¬ Live c χ (p, s, u) ↔
      (∃ n, Neg χ n ∧ Reach c χ (p, s, u) n) ∨
      (∃ δ, (p, !s, u ++ δ) ∈ Mu c χ) ∨
      (∃ δ, Reach c χ (p, s, u) (p, !s, u ++ δ)) := by
  classical
  constructor
  · intro hdead
    by_cases hn : Avoids χ (Cl c χ (p, s, u))
    · have hd : ¬ Consistent (Cl c χ (p, s, u)) :=
        fun hd => hdead (live_iff.mpr ⟨hn, hd⟩)
      simp only [Consistent, not_forall] at hd
      obtain ⟨a, b, hab, ha, hb, _⟩ := hd
      cases hab with
      | pair v w =>
        rcases mem_cl.mp ha with hma | hra <;> rcases mem_cl.mp hb with hmb | hrb
        · exact (hsat.2 (.pair v w) hma hmb).elim
        · obtain ⟨f, hf, hfa⟩ := mem_mu.mp hma
          obtain ⟨δ, hδ⟩ := collision_return hfa hrb
          exact Or.inr (Or.inl ⟨δ, mem_mu.mpr ⟨f, hf, hδ⟩⟩)
        · obtain ⟨f, hf, hfb⟩ := mem_mu.mp hmb
          obtain ⟨δ, hδ⟩ := collision_return hfb hra
          exact Or.inr (Or.inl ⟨δ, mem_mu.mpr ⟨f, hf, hδ⟩⟩)
        · exact Or.inr (Or.inr (collision_return hra hrb))
    · simp only [Avoids, not_forall, not_not] at hn
      obtain ⟨n, hnc, hneg⟩ := hn
      rcases mem_cl.mp hnc with hm | hr
      · exact (hsat.1 hm hneg).elim
      · exact Or.inl ⟨n, hneg, hr⟩
  · intro h hlive
    obtain ⟨S, hS, ha⟩ := hlive
    rcases h with ⟨n, hn, hr⟩ | ⟨δ, hm⟩ | ⟨δ, hr⟩
    · exact hS.avoids (hr.mem_of_closed hS.closed ha) hn
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha) (mu_subset hS hm)
    · exact hS.consistent.not_flip
        ((reach_extend p s u δ).mem_of_closed hS.closed ha)
        (hr.mem_of_closed hS.closed ha)

/-! ## Ternary mixed-variance examples

The variance is contravariant at arguments zero and two. The examples
exhibit each deadness case with a satisfiable background.
-/
namespace DualityExamples
open LeafHornExamples

/-- The mixed constructor example is satisfiable. -/
theorem mixed_sat : ∃ ρ, SatT arrow ρ mixed := ⟨low, low_solution⟩

/-- The mixed example has empty unit closure. -/
theorem mixed_mu_empty : Mu arrow mixed = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨a, ha, _⟩ := mem_mu.mp hb
  exact mixed_no_facts a ha

/-- The background premise is inhabited even without joint parity. -/
theorem mixed_background : Avoids mixed (Mu arrow mixed) ∧ Consistent (Mu arrow mixed) :=
  sat_iff_mu.mp mixed_sat

/-- The ternary example admits no joint parity assignment. -/
theorem no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    ∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i) := mixed_no_joint

/-- The two branches collide at z at the empty word. -/
theorem mixed_collision :
    Reach arrow mixed (false, false, [1]) (true, false, []) ∧
    Reach arrow mixed (false, false, [0]) (true, true, []) := by
  constructor
  · exact .step .refl (.move (.lefPop (a := fun _ => true) 1 (by simp [mixed])))
  · exact .step .refl (.move (.lefPop (a := fun _ => true) 0 (by simp [mixed])))

/-- Equation (15), with no extension needed: y⁺(1) → z⁺(ε) → y⁻(0). -/
theorem mixed_return : Moves arrow mixed (false, false, [1]) (false, true, [0]) := by
  have h : Move arrow mixed (false, false, [1]) (true, false, []) :=
    .lefPop (a := fun _ => true) 1 (by simp [mixed])
  exact (Relation.ReflTransGen.single h).tail
    (.lefPush (a := fun _ => true) 0 (by simp [mixed]))

/-- The mixed example has a return to an opposite signed atom. -/
theorem mixed_collision_return :
    ∃ δ, Reach arrow mixed (false, false, [1]) (false, true, [0] ++ δ) :=
  collision_return mixed_collision.1 mixed_collision.2

/-- The third child participates in the collision and opposite-sign return. -/
theorem third_child_return :
    Reach arrow mixed (false, false, [2]) (true, true, []) ∧
    Moves arrow mixed (false, false, [1]) (false, true, [2]) := by
  refine ⟨.step .refl (.move (.lefPop (a := fun _ => true) 2 (by simp [mixed]))), ?_⟩
  have h : Move arrow mixed (false, false, [1]) (true, false, []) :=
    .lefPop (a := fun _ => true) 1 (by simp [mixed])
  exact (Relation.ReflTransGen.single h).tail
    (.lefPush (a := fun _ => true) 2 (by simp [mixed]))

/-- The first seed alone is live, using the branching solution. -/
theorem mixed_zero_live : Live arrow mixed (false, false, [0]) := by
  refine ⟨configSet arrow branch, (sat_iff_sol _).mp branch_solution, ?_⟩
  simp [configSet, branch, arrow]

/-- The second seed alone is live as well. -/
theorem mixed_one_live : Live arrow mixed (false, false, [1]) := by
  let ρ : Bool → Tree 3 := fun i =>
    if i then DeciNSSE.Tree.top else DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.top)
  have hρ : SatT arrow ρ mixed := by
    simp [SatT, HoldsT, mixed, ρ, Function.comp_def, treeLe_refl]
  refine ⟨configSet arrow ρ, (sat_iff_sol _).mp hρ, ?_⟩
  simp [configSet, ρ, arrow]

/-- Singleton liveness is not joint liveness: the return path exposes the conflict. -/
theorem mixed_not_jointly_live : ¬ ∃ S, Sol arrow mixed S ∧
    (false, false, [0]) ∈ S ∧ (false, false, [1]) ∈ S := by
  rintro ⟨S, hS, hzero, hone⟩
  exact hS.consistent (.pair false [0]) hzero
    ((moves_reach mixed_return).mem_of_closed hS.closed hone)

/-- First deadness case: the forbidden constructor root itself. -/
theorem negative_root_witness :
    ∃ n, Neg mixed n ∧ Reach arrow mixed (false, false, []) n :=
  ⟨(false, false, []), .lef (a := fun _ => true) (by simp [mixed]), .refl⟩

/-- A forbidden root atom is not live. -/
theorem negative_root_dead : ¬ Live arrow mixed (false, false, []) :=
  (dead_iff mixed_background).mpr (Or.inl negative_root_witness)

/-- Second deadness case: a positive unit supplies the opposite descendant. -/
def forced : List (LitT 3 Unit) := [.bot ()]

/-- The forced-unit example is satisfiable. -/
theorem forced_sat : ∃ ρ, SatT arrow ρ forced := by
  exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, forced]⟩

/-- Unit closure contains the opposite signed atom. -/
theorem forced_opposite (u : List (Fin 3)) : ((), true, u) ∈ Mu arrow forced := by
  apply mem_mu.mpr
  exact ⟨((), true, []), .bot (by simp [forced]), by simpa using
    (reach_extend (c := arrow) (χ := forced) () true [] u)⟩

/-- An atom opposite a forced unit is dead. -/
theorem forced_dead (u : List (Fin 3)) : ¬ Live arrow forced ((), false, u) := by
  apply (dead_iff (sat_iff_mu.mp forced_sat)).mpr
  exact Or.inr (Or.inl ⟨[], by simpa using forced_opposite u⟩)

/-- Third deadness case: x ≤ f(x,x,x) returns x⁺(0) to x⁻(0). -/
def self : List (LitT 3 Unit) := [.lef () (fun _ => ())]

/-- The self-return example is satisfiable. -/
theorem self_sat : ∃ ρ, SatT arrow ρ self :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, self]⟩

/-- The self-return example reaches its opposite atom. -/
theorem self_return : Reach arrow self ((), false, [0]) ((), true, [0]) := by
  exact .step (.step .refl (.move (.lefPop (a := fun _ => ()) 0 (by simp [self]))))
    (.extend () true [] 0)

/-- The self-return seed is dead. -/
theorem self_dead : ¬ Live arrow self ((), false, [0]) := by
  apply (dead_iff (sat_iff_mu.mp self_sat)).mpr
  exact Or.inr (Or.inr ⟨[], by simpa using self_return⟩)

end DualityExamples

end DeciENSSE.Core.Mixed
