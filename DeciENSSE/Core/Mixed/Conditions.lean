import DeciENSSE.Core.Mixed.Duality

/-! # Three conditions for mixed existential entailment

Existential entailment reduces to three conditions on the least closures
of satisfiable systems, for arbitrary variance and every arity.

## Main declarations

- `CondI0`, `CondU`, `CondII`,
  `existsEntailsT_of_unsat`, `not_existsEntailsT_of_unsat`,
  `three_conditions_mixed`, `condII_iff_moves`.
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {X Z : Type*} {c : Fin n → Bool}
  {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

/-- The consequent's visible unit consequences are already forced. -/
def CondI0 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  restrict (Mu c ψ) ⊆ Mu c φ

/-- No live visible seed reaches a consequent negative unit. -/
def CondU (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ a, Live c φ a → ∀ n, Neg ψ n → ¬ Reach c ψ (visible a) n

/-- Every visible consequence of a live seed is already in its closure. -/
def CondII (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ∀ a, Live c φ a → ∀ b : Config n X,
    Reach c ψ (visible a) (visible b) → b ∈ Cl c φ a

/-- An unsatisfiable antecedent entails every existential consequent. -/
theorem existsEntailsT_of_unsat (hφ : ¬ ∃ ρ, SatT c ρ φ) : ExistsEntailsT c φ ψ := by
  intro ρ _ hρ
  exact (hφ ⟨ρ, hρ⟩).elim

/-- A satisfiable antecedent cannot entail an unsatisfiable consequent. -/
theorem not_existsEntailsT_of_unsat (hφ : ∃ ρ, SatT c ρ φ)
    (hψ : ¬ ∃ ρ, SatT c ρ ψ) : ¬ ExistsEntailsT c φ ψ := by
  intro h
  obtain ⟨ρ, hρ⟩ := hφ
  obtain ⟨σ, _, hσ⟩ := h ρ (fun _ => trivial) hρ
  exact hψ ⟨Sum.elim ρ σ, hσ⟩

/-- The least positive closure is a model when the system is satisfiable. -/
theorem sol_mu {V : Type*} {χ : List (LitT n V)} (hχ : ∃ ρ, SatT c ρ χ) :
    Sol c χ (Mu c χ) :=
  ⟨hull_closed _, (fun {_} => hull_facts _),
    (sat_iff_mu.mp hχ).1, (sat_iff_mu.mp hχ).2⟩

/-- A live singleton's least closure is itself a model. -/
theorem sol_cl {V : Type*} {χ : List (LitT n V)} {a : Config n V}
    (ha : Live c χ a) : Sol c χ (Cl c χ a) :=
  ⟨hull_closed _, (fun {_} => hull_facts _), (live_iff.mp ha).1, (live_iff.mp ha).2⟩

/-- Necessity: apply entailment to the least model. -/
theorem condI0_of_existsEntailsT (hφ : ∃ ρ, SatT c ρ φ)
    (h : ExistsEntailsT c φ ψ) : CondI0 c φ ψ := by
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_mu hφ)
  intro a ha
  rw [← he]
  exact mu_subset hT ha

/-- Necessity: a singleton extension avoids every negative unit. -/
theorem condU_of_existsEntailsT (h : ExistsEntailsT c φ ψ) : CondU c φ ψ := by
  intro a ha n hn hr
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_cl ha)
  have hat : visible a ∈ T := by
    change a ∈ restrict T
    rw [he]
    exact mem_cl.mpr (Or.inr .refl)
  exact hT.avoids (hr.mem_of_closed hT.closed hat) hn

/-- Necessity: restrict the extension of the singleton's least model. -/
theorem condII_of_existsEntailsT (h : ExistsEntailsT c φ ψ) : CondII c φ ψ := by
  intro a ha b hr
  obtain ⟨T, hT, he⟩ := (existsEntails_iff_sol_subset φ ψ).mp h _ (sol_cl ha)
  have hat : visible a ∈ T := by
    change a ∈ restrict T
    rw [he]
    exact mem_cl.mpr (Or.inr .refl)
  rw [← he]
  exact hr.mem_of_closed hT.closed hat

/-- Separate unit ancestry from visible-seed ancestry in a projected closure. -/
theorem mem_hull_visible {S : Set (Config n X)} {b : Config n (X ⊕ Z)} :
    b ∈ Hull c ψ (visible '' S) ↔
      b ∈ Mu c ψ ∨ ∃ a ∈ S, Reach c ψ (visible a) b := by
  constructor
  · rintro ⟨f, hf | ⟨a, ha, rfl⟩, hr⟩
    · exact Or.inl (mem_mu.mpr ⟨f, hf, hr⟩)
    · exact Or.inr ⟨a, ha, hr⟩
  · rintro (hm | ⟨a, ha, hr⟩)
    · obtain ⟨f, hf, hr⟩ := mem_mu.mp hm
      exact ⟨f, Or.inl hf, hr⟩
    · exact ⟨visible a, Or.inr ⟨a, ha, rfl⟩, hr⟩

/-- (I0) and (II) prevent new visible facts in the candidate extension. -/
theorem restrict_hull_subset (hI : CondI0 c φ ψ) (hII : CondII c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) :
    restrict (Hull c ψ (visible '' S)) ⊆ S := by
  intro b hb
  rcases mem_hull_visible.mp hb with hm | ⟨a, ha, hr⟩
  · exact mu_subset hS (hI hm)
  · exact cl_subset hS ha (hII a ⟨S, hS, ha⟩ b hr)

/-- Every negative-unit hit has one ancestor. -/
theorem avoids_hull_visible (hψ : ∃ ρ, SatT c ρ ψ) (hU : CondU c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) : Avoids ψ (Hull c ψ (visible '' S)) := by
  intro n hn hneg
  rcases mem_hull_visible.mp hn with hm | ⟨a, ha, hr⟩
  · exact (sat_iff_mu.mp hψ).1 hm hneg
  · exact hU a ⟨S, hS, ha⟩ n hneg hr

/-- A unit/seed collision returns a forced opposite visible descendant. -/
theorem no_unit_seed_collision (hI : CondI0 c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S)
    {q : X} {s : Bool} {u : List (Fin n)} (ha : (q, s, u) ∈ S)
    {v : X ⊕ Z} {t : Bool} {w : List (Fin n)}
    (hm : (v, t, w) ∈ Mu c ψ)
    (hr : Reach c ψ (visible (q, s, u)) (v, !t, w)) : False := by
  obtain ⟨f, hf, hfr⟩ := mem_mu.mp hm
  obtain ⟨δ, hδ⟩ := collision_return hfr hr
  have hforce : (q, !s, u ++ δ) ∈ Mu c φ := hI (mem_mu.mpr ⟨f, hf, hδ⟩)
  exact hS.consistent.not_flip
    ((reach_extend q s u δ).mem_of_closed hS.closed ha) (mu_subset hS hforce)

/-- Paired rules reduce every two-seed exclusion to (I0) or (II). -/
theorem consistent_hull_visible (hψ : ∃ ρ, SatT c ρ ψ)
    (hI : CondI0 c φ ψ) (hII : CondII c φ ψ)
    {S : Set (Config n X)} (hS : Sol c φ S) : Consistent (Hull c ψ (visible '' S)) := by
  intro p q hpq hp hq
  cases hpq with
  | pair v w =>
    rcases mem_hull_visible.mp hp with hmp | ⟨a, ha, hra⟩ <;>
      rcases mem_hull_visible.mp hq with hmq | ⟨b, hb, hrb⟩
    · exact (sat_iff_mu.mp hψ).2 (.pair v w) hmp hmq
    · rcases b with ⟨q, s, u⟩
      exact no_unit_seed_collision hI hS hb hmp hrb
    · rcases a with ⟨q, s, u⟩
      exact no_unit_seed_collision hI hS ha hmq hra
    · rcases b with ⟨q, s, u⟩
      obtain ⟨δ, hδ⟩ := collision_return hra hrb
      have hret := hII a ⟨S, hS, ha⟩ (q, !s, u ++ δ) hδ
      exact hS.consistent.not_flip
        ((reach_extend q s u δ).mem_of_closed hS.closed hb) (cl_subset hS ha hret)

/-- Sufficiency: the least closure of all visible seeds is an extension. -/
theorem existsEntailsT_of_three_conditions (hψ : ∃ ρ, SatT c ρ ψ)
    (hI : CondI0 c φ ψ) (hU : CondU c φ ψ) (hII : CondII c φ ψ) :
    ExistsEntailsT c φ ψ := by
  intro ρ _ hρ
  have hS := (sat_iff_sol ρ).mp hρ
  obtain ⟨σ, hσ⟩ := (extends_iff_hull ρ ψ).mpr
    ⟨avoids_hull_visible hψ hU hS, consistent_hull_visible hψ hI hII hS,
      restrict_hull_subset hI hII hS⟩
  exact ⟨σ, fun _ => trivial, hσ⟩

/-- The exact mixed leaf-Horn characterization. -/
theorem three_conditions_mixed (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧ CondII c φ ψ := by
  constructor
  · intro h
    exact ⟨condI0_of_existsEntailsT hφ h, condU_of_existsEntailsT h,
      condII_of_existsEntailsT h⟩
  · rintro ⟨hI, hU, hII⟩
    exact existsEntailsT_of_three_conditions hψ hI hU hII

/-- Move extensions to the seed, preserving liveness and shrinking closure. No antecedent
satisfiability premise is needed. -/
theorem condII_iff_moves : CondII c φ ψ ↔
    ∀ a b : Config n X, Live c φ a →
      Moves c ψ (visible a) (visible b) → b ∈ Cl c φ a := by
  constructor
  · intro h a b ha hr
    exact h a ha b (moves_reach hr)
  · intro h a ha b hr
    rcases a with ⟨p, s, u⟩
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    exact cl_extend_subset p s u α (h (p, s, u ++ α) b (live_extend α ha) hα)

/-! ## Semantic examples at ternary mixed variance -/
namespace ConditionsExamples
open LeafHornExamples

/-- Visible `false = y`, `true = x`; each child has its own hidden variable. Distinct hidden
children keep the reached hidden signs as sinks. -/
def separate : List (LitT 3 (Bool ⊕ Fin 3)) :=
  [.lef (.inl false) Sum.inr]

/-- The empty antecedent is satisfiable. -/
theorem empty_sat : ∃ ρ : Bool → Tree 3, SatT arrow ρ [] :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT]⟩

/-- The separate-variable consequent is satisfiable. -/
theorem separate_sat : ∃ ρ, SatT arrow ρ separate :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, separate]⟩

/-- The separate-variable consequent has no forced atoms. -/
theorem separate_mu_empty : Mu arrow separate = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro b hb
  obtain ⟨a, hf, _⟩ := mem_mu.mp hb
  cases hf <;> simp_all [separate]

/-- The positive unit condition holds for the separate-variable example. -/
theorem separate_condI0 : CondI0 arrow [] separate := by
  intro a ha
  change visible a ∈ Mu arrow separate at ha
  rw [separate_mu_empty] at ha
  exact ha.elim

/-- Hidden signs reached from a visible seed are sinks: the reverse rule requires the opposite
sign at that same hidden variable. -/
def envelope (S : Set (Config 3 Bool)) : Set (Config 3 (Bool ⊕ Fin 3)) :=
  {p | match p.1 with
    | .inl x => (x, p.2) ∈ S
    | .inr i => p.2.1 = arrow i}

/-- The displayed envelope is closed under all clauses. -/
theorem envelope_closed {S : Set (Config 3 Bool)} (hS : Closed arrow [] S) :
    Closed arrow separate (envelope S) := by
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
    (hr : Reach arrow separate (visible a) (visible b)) : b ∈ Cl arrow [] a := by
  exact hr.mem_of_closed (envelope_closed (hull_closed _))
    (show visible a ∈ envelope (Cl arrow [] a) from mem_cl.mpr (Or.inr .refl))

/-- The singleton closure condition holds in the separate-variable example. -/
theorem separate_condII : CondII arrow [] separate :=
  fun _ _ _ hr => separate_visible_reach hr

/-- A root atom is live over the empty antecedent. -/
theorem empty_root_live : Live arrow ([] : List (LitT 3 Bool)) (false, false, []) := by
  refine ⟨configSet arrow (fun _ => DeciNSSE.Tree.top), (sat_iff_sol _).mp ?_, ?_⟩
  · simp [SatT]
  · simp [configSet]

/-- The separate-variable example fails the negative unit condition. -/
theorem separate_not_condU : ¬ CondU arrow [] separate := by
  intro h
  exact h (false, false, []) empty_root_live (visible (false, false, []))
    (.lef (a := Sum.inr) (by simp [separate])) .refl

/-- Direct check against the tree semantics: visible y = top has no witness. -/
theorem separate_not_entails : ¬ ExistsEntailsT arrow [] separate := by
  intro h
  obtain ⟨σ, _, hσ⟩ := h (fun _ => DeciNSSE.Tree.top) (fun _ => trivial) (by simp [SatT])
  have hle := hσ (.lef (.inl false) Sum.inr) (by simp [separate])
  exact leaf_node_nil arrow σ false
    (((leGen_iff_leaf _ _ _).mp hle).1 (by simp))

/-- All satisfiability premises hold, but dropping U makes the test unsound. -/
theorem units_cannot_be_dropped :
    (∃ ρ : Bool → Tree 3, SatT arrow ρ []) ∧
    (∃ ρ, SatT arrow ρ separate) ∧
    CondI0 arrow [] separate ∧ CondII arrow [] separate ∧
    ¬ CondU arrow [] separate ∧ ¬ ExistsEntailsT arrow [] separate :=
  ⟨empty_sat, separate_sat, separate_condI0, separate_condII,
    separate_not_condU, separate_not_entails⟩

/-- The characterization itself detects exactly the missing condition U. -/
theorem separate_characterization :
    ExistsEntailsT arrow [] separate ↔
      CondI0 arrow [] separate ∧ CondU arrow [] separate ∧ CondII arrow [] separate :=
  three_conditions_mixed empty_sat separate_sat

/-- Equation (15), reusing the `mixed = [y ≤ f(z,z,z)]`. -/
theorem collision_15 :
    Reach arrow mixed (false, false, [1]) (true, false, []) ∧
    Reach arrow mixed (false, false, [0]) (true, true, []) ∧
    Moves arrow mixed (false, false, [1]) (false, true, [0]) :=
  ⟨DualityExamples.mixed_collision.1, DualityExamples.mixed_collision.2,
    DualityExamples.mixed_return⟩

/-- Put that same mixed constraint in the visible part of a consequent. -/
def embedded : List (LitT 3 (Bool ⊕ Unit)) :=
  [.lef (.inl false) (fun _ => .inl true)]

/-- The visible embedding of the mixed system is satisfiable. -/
theorem embedded_sat : ∃ ρ, SatT arrow ρ embedded :=
  ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, embedded]⟩

/-- The embedded mixed system admits no joint parity assignment. -/
theorem embedded_no_joint_parity : ¬ ∃ s : Bool ⊕ Unit → Bool,
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) ∧
    (∀ i : Fin 3, s (.inl true) = Bool.xor (s (.inl false)) (arrow i)) := by
  rintro ⟨s, hφ, _⟩
  exact mixed_no_parity ⟨s ∘ Sum.inl, hφ⟩

/-- Direct semantic proof, with a satisfiable antecedent and no joint parity. -/
theorem embedded_entails : ExistsEntailsT arrow mixed embedded := by
  intro ρ _ hρ
  refine ⟨fun _ => DeciNSSE.Tree.bot, fun _ => trivial, ?_⟩
  simpa [SatT, HoldsT, embedded, mixed, Function.comp_def] using hρ

/-- Non-vacuity of all three conditions at genuinely mixed variance. -/
theorem embedded_conditions :
    CondI0 arrow mixed embedded ∧ CondU arrow mixed embedded ∧ CondII arrow mixed embedded :=
  (three_conditions_mixed DualityExamples.mixed_sat embedded_sat).mp embedded_entails

/-- Pure visible returns obey the singleton closure condition. -/
theorem embedded_pure_condition : ∀ a b : Config 3 Bool, Live arrow mixed a →
    Moves arrow embedded (visible a) (visible b) → b ∈ Cl arrow mixed a :=
  condII_iff_moves.mp embedded_conditions.2.2

/-- The same non-parity consequent fails over the empty antecedent. -/
theorem embedded_empty_no_joint_parity :
    ¬ ∃ s : Bool ⊕ Unit → Bool, ∀ i : Fin 3,
      s (.inl true) = Bool.xor (s (.inl false)) (arrow i) := mixed_no_joint

/-- The empty antecedent does not entail the embedded mixed system. -/
theorem embedded_empty_not_entails : ¬ ExistsEntailsT arrow [] embedded := by
  intro h
  obtain ⟨σ, _, hσ⟩ := h (fun _ => DeciNSSE.Tree.top) (fun _ => trivial) (by simp [SatT])
  have hle := hσ (.lef (.inl false) (fun _ => .inl true)) (by simp [embedded])
  exact leaf_node_nil arrow (fun _ => DeciNSSE.Tree.top) false
    (((leGen_iff_leaf _ _ _).mp hle).1 (by simp))

/-- Both collision seeds occur in one empty-antecedent model. Neither is a root. -/
def collisionAssignment : Bool → Tree 3 :=
  fun i => if i then DeciNSSE.Tree.bot else
    DeciNSSE.Tree.node (fun i => if i = 1 then DeciNSSE.Tree.top else DeciNSSE.Tree.bot)

/-- Two distinct words occur together in the displayed assignment. -/
theorem collision_seeds :
    (false, false, [0]) ∈ configSet arrow collisionAssignment ∧
    (false, false, [1]) ∈ configSet arrow collisionAssignment := by
  simp [configSet, collisionAssignment, arrow]

/-- The embedded system returns between opposite signed visible atoms. -/
theorem embedded_return :
    Moves arrow embedded (visible (false, false, [1])) (visible (false, true, [0])) := by
  have h : Move arrow embedded (visible (false, false, [1])) (.inl true, false, []) :=
    Move.lefPop (c := arrow) (χ := embedded)
      (a := fun _ => .inl true) 1 (by simp [embedded])
  exact (Relation.ReflTransGen.single h).tail
    (Move.lefPush (c := arrow) (χ := embedded)
      (a := fun _ => .inl true) 0 (by simp [embedded]))

/-- A concrete two-seed collision is detected by the single-seed condition II. -/
theorem embedded_empty_not_condII : ¬ CondII arrow [] embedded := by
  intro h
  have hS : Sol arrow [] (configSet arrow collisionAssignment) :=
    (sat_iff_sol _).mp (by simp [SatT])
  have hc := h (false, false, [1]) ⟨_, hS, collision_seeds.2⟩
    (false, true, [0]) (moves_reach embedded_return)
  exact hS.consistent (.pair false [0]) collision_seeds.1
    (cl_subset hS collision_seeds.2 hc)

/-- The characterization also rejects this example through II. -/
theorem embedded_collision_not_entails : ¬ ExistsEntailsT arrow [] embedded :=
  fun h => embedded_empty_not_condII
    ((three_conditions_mixed empty_sat embedded_sat).mp h).2.2

/-- Non-vacuity for both unsatisfiable-system branches of the characterization. -/
theorem contradictory_units {V : Type*} (v : V) :
    ¬ ∃ ρ, SatT arrow ρ [.bot v, .top v] := by
  rintro ⟨ρ, hρ⟩
  have hb : ρ v = DeciNSSE.Tree.bot := hρ (.bot v) (by simp)
  have ht : ρ v = DeciNSSE.Tree.top := hρ (.top v) (by simp)
  exact DeciNSSE.Tree.bot_ne_top (hb.symm.trans ht)

/-- An inconsistent antecedent entails every consequent. -/
theorem unsat_antecedent_entails :
    ExistsEntailsT arrow [.bot false, .top false] separate :=
  existsEntailsT_of_unsat (contradictory_units false)

/-- A satisfiable antecedent cannot entail an inconsistent consequent. -/
theorem unsat_consequent_not_entails : ¬ ExistsEntailsT arrow ([] : List (LitT 3 Bool))
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
