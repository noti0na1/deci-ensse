import DeciENSSE.Core.ClassesLanguage
import DeciENSSE.Core.Final

/-! # Regular and finite trees over {⊥, fₙ}

Regular Horn hulls and finite least solutions transfer existential entailment
to regular and finite trees. All three decisions cover arity zero.

## Main declarations

- `Sat_fin`
- `finite_sat_iff`
- `regular_extension`
- `existsEntailsReg_iff`
- `existsEntailsFin_iff`
- `decideSatFin`
- `decideExistsEntailsFin`
- `decideExistsEntailsReg`
-/

namespace DeciENSSE.Core
variable {n : ℕ}

/-- Satisfiability with every variable assigned a finite tree. -/
def Sat_fin {V : Type*} (χ : List (Lit n V)) : Prop :=
  ∃ ρ, (∀ v, IsFiniteTree (ρ v)) ∧ Sat ρ χ

/-- Finite satisfiability is consistency with finite least-solution components. -/
theorem finite_sat_iff {V : Type*} (χ : List (Lit n V)) :
    Sat_fin χ ↔ (∃ ρ, Sat ρ χ) ∧ ∀ y, {t | (y, t) ∈ Mu χ}.Finite := by
  constructor
  · rintro ⟨ρ, hf, hs⟩
    exact ⟨⟨ρ, hs⟩, fun y => (hf y).subset fun _ h =>
      ((sat_iff_sol ρ).mp hs).mu_subset h⟩
  · rintro ⟨hs, hf⟩
    exact ⟨assignmentOf (Mu χ) mu_closed.prefixClosed, hf,
      (sat_iff_sol _).mpr (mu_sol hs)⟩

namespace Classes
open DeciENSSE.Core.Bound
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite languages have a uniform strict length bound. -/
theorem finite_length_bound {L : Set (List (Fin n))} (h : L.Finite) :
    ∃ n, ∀ w ∈ L, w.length < n := by
  obtain ⟨n, hn⟩ := (h.image List.length).bddAbove
  exact ⟨n + 1, fun w hw => Nat.lt_succ_of_le (hn ⟨w, hw, rfl⟩)⟩

/-- Finite least-solution components imply finite singleton-closure components. -/
theorem cl_component_finite {χ : List (Lit n V)}
    (hf : ∀ y, {t | (y, t) ∈ Mu χ}.Finite) (a : Config n V) (y : V) :
    {t | (y, t) ∈ Cl χ a}.Finite := by
  obtain ⟨N, hn⟩ := finite_length_bound (hf y)
  apply (List.finite_length_le (Fin n) (N + a.2.length)).subset
  intro t ht
  rcases cl_membership.mp ht with hm | ⟨s, hs, e, he, hq, hp⟩
  · have := hn t (mu_membership.mpr hm)
    dsimp; omega
  · have hlen := hp.length_le
    simp only [List.length_drop] at hlen
    by_cases he0 : e = 0
    · dsimp; omega
    · have hne : (Q χ y (t.take e)).Nonempty := hq.mono Finset.inter_subset_right
      have hc := cone_prefix hne (show e - 1 < (t.take e).length by
        simp only [List.length_take]; omega)
      have hm : (y, t.take (e - 1)) ∈ Mu χ := by
        apply mu_membership.mpr
        simpa only [List.take_take, Nat.min_eq_left (show e - 1 ≤ e by omega)] using
          Finset.not_disjoint_iff_nonempty_inter.mp hc
      have hb := hn _ hm
      simp only [List.length_take] at hb
      dsimp; omega

/-- A finite recognized language contains no word as long as the state count. -/
theorem finite_dfa_length {S : Type*} [Fintype S] (M : LDFA (Fin n) S)
    (F : Set S) (hf : {w | M.run w ∈ F}.Finite) {w : List (Fin n)}
    (hw : M.run w ∈ F) : w.length < Fintype.card S := by
  by_contra hn
  let D : DFA (Fin n) S := ⟨M.step, M.start, F⟩
  obtain ⟨q, a, b, c, _, _, hb, ha, hloop, hc⟩ :=
    D.evalFrom_split (x := w) (s := M.start) (by omega) rfl
  change M.runFrom M.start a = q at ha
  change M.runFrom q b = q at hloop
  change M.runFrom q c = M.run w at hc
  obtain ⟨n, hn⟩ := finite_length_bound hf
  have pump : ∀ k, M.runFrom q ((List.replicate k b).flatten) = q := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ, List.flatten_cons,
        LDFA.runFrom_append, hloop] using ih
  have hp : M.run (a ++ (List.replicate n b).flatten ++ c) ∈ F := by
    simpa [LDFA.run, LDFA.runFrom_append, ha, pump, hc] using hw
  have hlen := hn _ hp
  have hbpos := List.length_pos_iff.mpr hb
  simp only [List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate, Nat.nsmul_eq_mul] at hlen
  have : n ≤ n * b.length := Nat.le_mul_of_pos_right n hbpos
  omega

/-- A computable (powerset lower-automaton) cycle test. -/
def FiniteMuTest (χ : List (Lit n V)) : Prop :=
  ∀ y, ∀ w : Fin (Fintype.card (Finset V)) → Fin n,
    Disjoint (Q χ y (List.ofFn w)) (LowF χ)

instance instDecidableFiniteMuTest (χ : List (Lit n V)) : Decidable (FiniteMuTest χ) :=
  inferInstanceAs (Decidable (∀ y, ∀ w : Fin (Fintype.card (Finset V)) → Fin n,
    Disjoint (Q χ y (List.ofFn w)) (LowF χ)))

/-- The bounded lower-automaton test recognizes finite least-solution components. -/
theorem finiteMuTest_iff (χ : List (Lit n V)) :
    FiniteMuTest χ ↔ ∀ y, {t | (y, t) ∈ Mu χ}.Finite := by
  constructor
  · intro h y
    apply (List.finite_length_lt (Fin n) (Fintype.card (Finset V))).subset
    intro w hw
    change w.length < Fintype.card (Finset V)
    by_contra hn
    have he : (w.take (Fintype.card (Finset V))).length =
        Fintype.card (Finset V) := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hp := mu_closed.prefixClosed y (w.take (Fintype.card (Finset V)))
      (w.drop (Fintype.card (Finset V))) (by simpa using hw)
    have hd := h y (fun i => (w.take (Fintype.card (Finset V))).get
      ⟨i.val, by omega⟩)
    have heq : List.ofFn (fun i : Fin (Fintype.card (Finset V)) =>
        (w.take (Fintype.card (Finset V))).get ⟨i.val, by omega⟩) =
        w.take (Fintype.card (Finset V)) := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using he.symm
      · intros; simp
    rw [heq] at hd
    exact (Finset.not_disjoint_iff_nonempty_inter.mpr (mu_membership.mp hp)) hd
  · intro h y w
    apply Finset.disjoint_left.mpr
    intro r hr hl
    have hd : (Q χ y (List.ofFn w) ∩ LowF χ).Nonempty := ⟨r, Finset.mem_inter.mpr ⟨hr, hl⟩⟩
    have hm : (y, List.ofFn w) ∈ Mu χ :=
      mu_membership.mpr hd
    have hf : {w | (lower χ y).run w ∈ {q | (q ∩ LowF χ).Nonempty}}.Finite := by
      change {w | (Q χ y w ∩ LowF χ).Nonempty}.Finite
      simpa only [← mu_membership] using h y
    have hlength := finite_dfa_length (lower χ y) _ hf (mu_membership.mp hm)
    simp at hlength

end Classes

/-- Executable finite satisfiability, using the lower automaton and root clashes. -/
def decideSatFin {V : Type*} [Fintype V] [DecidableEq V] (χ : List (Lit n V)) :
    Decidable (Sat_fin χ) := by
  letI := Bound.decideSat χ
  exact decidable_of_iff ((∃ ρ, Sat ρ χ) ∧ Classes.FiniteMuTest χ)
    (by rw [finite_sat_iff, Classes.finiteMuTest_iff])

namespace Classes
variable {X Z : Type*}

/-- Testing the least solution and singleton closures suffices for the reverse class transfer. No
assumption on extensions is used here. -/
theorem entails_of_class {C : BFTreeN n → Prop} {φ : List (Lit n X)}
    {ψ : List (Lit n (X ⊕ Z))}
    (hmu : ∀ x, C (assignmentOf (Mu φ) mu_closed.prefixClosed x))
    (hcl : ∀ a x, C (assignmentOf (Cl φ a) (cl_closed a).prefixClosed x))
    (he : ExistsEntailsIn C φ ψ) : ExistsEntails φ ψ := by
  classical
  by_cases hφ : ∃ ρ, Sat ρ φ
  · have hmin := he _ hmu ((sat_iff_sol _).mpr (mu_sol hφ))
    obtain ⟨σ, _, hσ⟩ := hmin
    have hψ : ∃ ρ, Sat ρ ψ := ⟨_, hσ⟩
    apply (three_conditions hφ hψ).mpr
    have hproj : Mu φ ∈ Projected ψ :=
      (projected_configSet _ ψ).mpr ⟨σ, hσ⟩
    refine ⟨((projected_iff hψ _).mp hproj).1, ?_, ?_⟩
    · intro a ha
      obtain ⟨σ, _, hσ⟩ := he _ (hcl a) ((sat_iff_sol _).mpr (cl_sol ha))
      have hp := (projected_configSet _ ψ).mpr ⟨σ, hσ⟩
      exact ((projected_iff hψ _).mp hp).2.1 (mem_cl a)
    · intro a ha b hb
      obtain ⟨σ, _, hσ⟩ := he _ (hcl a) ((sat_iff_sol _).mpr (cl_sol ha))
      have hp := (projected_configSet _ ψ).mpr ⟨σ, hσ⟩
      exact ((projected_iff hψ _).mp hp).2.2 a (mem_cl a) (Or.inr hb)
  · exact existsEntails_of_unsat hφ

/-- The least extension below an existing extension. -/
theorem hull_extension {C : BFTreeN n → Prop} {ψ : List (Lit n (X ⊕ Z))}
    (ρ : X → BFTreeN n) (σ : Z → BFTreeN n) (hs : Sat (Sum.elim ρ σ) ψ)
    (hg : ∀ z, C (assignmentOf (Hull ψ (visible '' configSet ρ))
      (hull_closed _).prefixClosed (.inr z))) :
    ∃ τ, (∀ z, C (τ z)) ∧ Sat (Sum.elim ρ τ) ψ := by
  let H := Hull ψ (visible '' configSet ρ)
  have hsol := (sat_iff_sol _).mp hs
  have hsub : H ⊆ configSet (Sum.elim ρ σ) :=
    (hull_least _).2.2 _ hsol.closed (by
      rintro a (ha | ⟨b, hb, rfl⟩)
      · exact hsol.facts ha
      · exact hb)
  have hH : Sol ψ H := ⟨hull_closed _, fun _ ha => Or.inl (facts_subset_mu ha),
      fun _ ha => hsol.avoids (hsub ha)⟩
  let τ := assignmentOf H (hull_closed _).prefixClosed
  have hv : ∀ x, τ (.inl x) = ρ x := by
    intro x
    apply BFTreeN.ext
    apply Set.Subset.antisymm
    · intro w hw; exact hsub hw
    · intro w hw
      exact hull_contains _ (Or.inr ⟨(x,w), hw, rfl⟩)
  refine ⟨fun z => τ (.inr z), hg, ?_⟩
  have ht : Sum.elim ρ (fun z => τ (.inr z)) = τ := by
    funext v; cases v with
    | inl x => exact (hv x).symm
    | inr z => rfl
  rw [ht]
  exact (sat_iff_sol _).mpr hH

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

omit [DecidableEq X] in
/-- A finite family of finite trees has finitely many configurations. -/
theorem finite_configSet (ρ : X → BFTreeN n) (hf : ∀ x, IsFiniteTree (ρ x)) :
    (configSet ρ).Finite := by
  have h := Set.finite_iUnion (fun x => (hf x).image (fun w => (x,w)))
  apply h.subset
  rintro ⟨x,w⟩ hw
  exact Set.mem_iUnion.mpr ⟨x, w, hw, rfl⟩

/-- Finite seed sets and finite least solutions give finite Horn hulls. -/
theorem finite_hull {V : Type*} [Fintype V] [DecidableEq V]
    {χ : List (Lit n V)} (hf : ∀ y, {t | (y,t) ∈ Mu χ}.Finite)
    {A : Set (Config n V)} (hA : A.Finite) (y : V) :
    {t | (y,t) ∈ Hull χ A}.Finite := by
  apply ((hf y).union (hA.biUnion fun a _ => cl_component_finite hf a y)).subset
  rintro t (ht | ⟨a,ha,hr⟩)
  · exact Or.inl ht
  · exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, Or.inr hr⟩⟩)

end Classes

/-- The finite-tree transfer theorem, including both satisfiability exceptions. -/
theorem existsEntailsFin_iff {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsIn IsFiniteTree φ ψ ↔
      ¬ Sat_fin φ ∨ (Sat_fin ψ ∧ ExistsEntails φ ψ) := by
  classical
  constructor
  · intro he
    by_cases hf : Sat_fin φ
    · right
      obtain ⟨ρ, hρ, hs⟩ := hf
      obtain ⟨σ, hσ, ht⟩ := he ρ hρ hs
      have hμ := (finite_sat_iff φ).mp ⟨ρ, hρ, hs⟩
      exact ⟨⟨Sum.elim ρ σ, by intro v; cases v <;> simp_all, ht⟩,
        Classes.entails_of_class hμ.2 (Classes.cl_component_finite hμ.2) he⟩
    · exact Or.inl hf
  · rintro (hf | ⟨hf, he⟩) ρ hρ hs
    · exact (hf ⟨ρ, hρ, hs⟩).elim
    · obtain ⟨σ, _, ht⟩ := he ρ (fun _ => trivial) hs
      apply Classes.hull_extension ρ σ ht
      intro z
      exact Classes.finite_hull ((finite_sat_iff ψ).mp hf).2
        ((Classes.finite_configSet ρ hρ).image visible) (.inr z)

/-- Unconditional computable finite-tree existential entailment. -/
def decideExistsEntailsFin {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsFiniteTree φ ψ) := by
  letI := decideExistsEntails φ ψ
  letI := decideSatFin φ
  letI := decideSatFin ψ
  exact decidable_of_iff (¬ Sat_fin φ ∨ (Sat_fin ψ ∧ ExistsEntails φ ψ))
    (existsEntailsFin_iff φ ψ).symm

/-- Satisfiability with regular witnesses is equivalent to satisfiability. -/
theorem regular_sat_iff {V : Type*} [Fintype V] [DecidableEq V]
    (χ : List (Lit n V)) :
    (∃ ρ, (∀ v, IsRegularTree (ρ v)) ∧ Sat ρ χ) ↔ ∃ ρ, Sat ρ χ := by
  constructor
  · rintro ⟨ρ,_,hs⟩; exact ⟨ρ,hs⟩
  · intro hs
    exact ⟨assignmentOf (Mu χ) mu_closed.prefixClosed,
      Classes.mu_regular χ, (sat_iff_sol _).mpr (mu_sol hs)⟩

/-- A regular visible solution admitting an extension admits a regular one. -/
theorem regular_extension {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {ψ : List (Lit n (X ⊕ Z))} (ρ : X → BFTreeN n)
    (hr : ∀ x, IsRegularTree (ρ x)) (σ : Z → BFTreeN n)
    (hs : Sat (Sum.elim ρ σ) ψ) :
    ∃ τ, (∀ z, IsRegularTree (τ z)) ∧ Sat (Sum.elim ρ τ) ψ := by
  apply Classes.hull_extension ρ σ hs
  let η : X ⊕ Z → BFTreeN n := Sum.elim ρ (fun _ => BFTreeN.bot)
  have he : configSet η = visible '' configSet ρ := by
    ext a
    rcases a with ⟨x,w⟩
    cases x with
    | inl x => simp [configSet,η,visible]
    | inr z => simp [configSet,η,visible]
  have hη : ∀ v, IsRegularTree (η v) := by
    intro v
    cases v with
    | inl x => exact hr x
    | inr z => exact Classes.reg_finite Set.finite_empty
  intro z
  have h := Classes.hull_regular ψ η hη (.inr z)
  change Classes.Reg {w | (.inr z,w) ∈ Hull ψ (configSet η)} at h
  change Classes.Reg {w | (.inr z,w) ∈ Hull ψ (visible '' configSet ρ)}
  simpa only [he] using h

/-- Regular-tree and arbitrary-tree existential entailment agree. -/
theorem existsEntailsReg_iff {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsIn IsRegularTree φ ψ ↔ ExistsEntails φ ψ := by
  constructor
  · exact Classes.entails_of_class (Classes.mu_regular φ) (Classes.cl_regular φ)
  · intro he ρ hr hs
    obtain ⟨σ,_,ht⟩ := he ρ (fun _ => trivial) hs
    exact regular_extension ρ hr σ ht

/-- Unconditional computable regular-tree existential entailment. -/
def decideExistsEntailsReg {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    Decidable (ExistsEntailsIn IsRegularTree φ ψ) := by
  letI := decideExistsEntails φ ψ
  exact decidable_of_iff (ExistsEntails φ ψ) (existsEntailsReg_iff φ ψ).symm

/-- Boolean correctness of the unconditional finite-tree decision. -/
theorem decideExistsEntailsFin_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsFin φ ψ) = true ↔
      ExistsEntailsIn IsFiniteTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsFin φ ψ)

/-- Boolean correctness of the unconditional regular-tree decision. -/
theorem decideExistsEntailsReg_correct {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    @decide _ (decideExistsEntailsReg φ ψ) = true ↔
      ExistsEntailsIn IsRegularTree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsReg φ ψ)


end DeciENSSE.Core
