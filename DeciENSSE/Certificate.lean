import DeciENSSE.Core.Mixed.ExtractModel
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.TopFree

/-! # Counterexample words and their countermodels

`CounterexampleWord` formalizes the three kinds of counterexample words of
`def:as-certificate`, including the signed variables and the requirement (U)
for hole words. The three `*_word_iff` theorems prove the sentences following
that definition. Paths in the hole constructor follow the paper: `u` is the
output path and `t` is the seed path, so the separator word has length
`u.length + t.length + 1`.

In the `CounterexampleWord` namespace, `seeds` and `observations` are exactly
the sets A and O of `lem:as-countermodel`, represented by a set and a list.
`hull_model` and `countermodel` prove item (1), while
`observations_no_extension` proves item (2) for every assignment satisfying O.
`bounds_iff` and `pinned_countermodels` prove item (3) uniformly for arbitrary,
regular, and finite trees, including arity zero. Ground bounds are a separate
conjunction with the flat system, since they are not flat literals.

`gadget_countermodel` proves item (4), retaining the given visible assignment
and restricting it to the original variables. Its class parameter only needs
`TopFree.HasWitnesses`, available for all three tree classes.

The consequent need not be assumed satisfiable for these countermodels.
The antecedent satisfiability hypothesis is used for the least unit model and
the extracted-hole characterization. The countermodel theorems are existence
statements; they do not assert that the countermodels are computable.
-/

namespace DeciENSSE
open DeciNSSE Core.Full Core.Mixed

variable {n : ℕ} {X Z : Type*}
  [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

/-- The three kinds of counterexample words of `def:as-certificate`. -/
inductive CertificateKind where
  | conditionI | conditionU | hole

/-- A word and its signed variables, with evidence that it is a certificate.
The kind index makes existence of each alternative a separate proposition. -/
inductive CounterexampleWord (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) : CertificateKind → Type _ where
  | ofI (q : X × Bool) (w : List (Fin n))
      (forced : (Sum.inl q.1, q.2, w) ∈ Mu c ψ)
      (missing : (q.1, q.2, w) ∉ Mu c φ) : CounterexampleWord c φ ψ .conditionI
  | ofU (p : X × Bool) (w : List (Fin n))
      (live : Live c φ (p.1, p.2, w)) (dead : DeadU c ψ p w) :
      CounterexampleWord c φ ψ .conditionU
  | ofHole (p q : X × Bool) (u t : List (Fin n)) (unit : CondU c φ ψ)
      (hole : (extractSelf c φ ψ p q).IsHole u t) : CounterexampleWord c φ ψ .hole

/-- The first sentence after `def:as-certificate`. -/
theorem conditionI_word_iff :
    Nonempty (CounterexampleWord c φ ψ .conditionI) ↔ ¬ CondI0 c φ ψ := by
  classical
  constructor
  · rintro ⟨w⟩ h
    cases w with
    | ofI q w hf hn => exact hn (h hf)
  · intro h
    obtain ⟨⟨q, s, w⟩, hf, hn⟩ := Set.not_subset.mp h
    exact ⟨.ofI (q, s) w hf hn⟩

/-- The second sentence after `def:as-certificate`. -/
theorem conditionU_word_iff :
    Nonempty (CounterexampleWord c φ ψ .conditionU) ↔ ¬ CondU c φ ψ := by
  classical
  rw [condU_iff]
  constructor
  · rintro ⟨w⟩ h
    cases w with
    | ofU p w hl hd => exact h p.1 p.2 w hd hl
  · intro h
    push Not at h
    obtain ⟨x, s, w, hd, hl⟩ := h
    exact ⟨.ofU (x, s) w hl hd⟩

/-- The third sentence after `def:as-certificate`; (U) is essential here. -/
theorem hole_word_iff (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ) :
    Nonempty (CounterexampleWord c φ ψ .hole) ↔ ¬ CondII c φ ψ := by
  classical
  rw [condII_iff_no_holes hφ hU]
  constructor
  · rintro ⟨w⟩ h
    cases w with
    | ofHole p q u t _ hh => exact h p q ⟨u, t, hh⟩
  · intro h
    push Not at h
    obtain ⟨p, q, u, t, hh⟩ := h
    exact ⟨.ofHole p q u t hU hh⟩

namespace CounterexampleWord
variable {k : CertificateKind}

/-- Word length, counting the separator in the hole case. -/
def length : CounterexampleWord c φ ψ k → ℕ
  | .ofI _ w _ _ => w.length
  | .ofU _ w _ _ => w.length
  | .ofHole _ _ u t _ _ => u.length + t.length + 1

/-- The set A in `lem:as-countermodel`: empty or a singleton. -/
def seeds : CounterexampleWord c φ ψ k → Set (Config n X)
  | .ofI _ _ _ _ => ∅
  | .ofU p w _ _ => {(p.1, p.2, w)}
  | .ofHole p _ _ t _ _ => {(p.1, p.2, t)}

/-- The list O in `lem:as-countermodel`: one or two signed observations. -/
def observations : CounterexampleWord c φ ψ k → List (Core.Mixed.Observation n X)
  | .ofI q w _ _ => [((q.1, q.2, w), false)]
  | .ofU p w _ _ => [((p.1, p.2, w), true)]
  | .ofHole p q u t _ _ => [((p.1, p.2, t), true), ((q.1, q.2, u), false)]

/-- Certificates use at most two observations. -/
theorem observations_length (w : CounterexampleWord c φ ψ k) :
    w.observations.length ≤ 2 := by
  cases w <;> simp [observations]

/-- `lem:as-countermodel`(1): `H_φ(A)` is a model of `φ`. -/
theorem hull_model (w : CounterexampleWord c φ ψ k) (hφ : ∃ ρ, SatT c ρ φ) :
    Sol c φ (Hull c φ w.seeds) := by
  cases w with
  | ofI q w hf hn => exact sol_mu hφ
  | ofU p w hl hd => exact sol_cl hl
  | ofHole p q u t hU hh =>
    exact sol_cl ((extractSelf_isHoleS_iff p q hφ hU u t).mp hh).1

/-- The exact observations hold in any decoding of the certificate's hull. -/
theorem observations_of_configSet (w : CounterexampleWord c φ ψ k)
    (hφ : ∃ ρ, SatT c ρ φ) {ρ : X → Tree n}
    (he : configSet c ρ = Hull c φ w.seeds) :
    ∀ o ∈ w.observations, o.Holds c ρ := by
  cases w with
  | ofI q w hf hn => simpa [observations, Core.Mixed.Observation.Holds, he, seeds, Mu] using hn
  | ofU p w hl hd =>
    simpa [observations, Core.Mixed.Observation.Holds, he, seeds] using
      (subset_hull (c := c) (χ := φ) {(p.1, p.2, w)} (Set.mem_singleton _))
  | ofHole p q u t hU hh =>
    have hn := ((extractSelf_isHoleS_iff p q hφ hU u t).mp hh).2.2
    have ha := subset_hull (c := c) (χ := φ) {(p.1, p.2, t)} (Set.mem_singleton _)
    simpa [observations, Core.Mixed.Observation.Holds, he, seeds, Cl] using And.intro ha hn

/-- `lem:as-countermodel`(2), for every assignment satisfying `O`. -/
theorem observations_no_extension (w : CounterexampleWord c φ ψ k)
    (hφ : ∃ ρ, SatT c ρ φ) {ρ : X → Tree n}
    (ho : ∀ o ∈ w.observations, o.Holds c ρ) :
    ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  rintro ⟨σ, hσ⟩
  have hs := (sat_iff_sol _).mp hσ
  cases w with
  | ofI q w hf hn =>
    have hd : (q.1, q.2, w) ∉ configSet c ρ := ho ((q.1, q.2, w), false) (by simp [observations])
    exact hd (mu_subset hs hf)
  | ofU p w hl hd =>
    have ha : (p.1, p.2, w) ∈ configSet c ρ := ho ((p.1, p.2, w), true) (by simp [observations])
    obtain ⟨a, hn, hr⟩ := (deadU_iff_reach_neg c ψ p w).mp hd
    exact hs.avoids (hr.mem_of_closed hs.closed ha) hn
  | ofHole p q u t hU hh =>
    have ha : (p.1, p.2, t) ∈ configSet c ρ := ho ((p.1, p.2, t), true) (by simp [observations])
    have hb : (q.1, q.2, u) ∉ configSet c ρ := ho ((q.1, q.2, u), false) (by simp [observations])
    have hm := ((extractSelf_isHoleS_iff p q hφ hU u t).mp hh).2.1
    exact hb ((moves_reach hm).mem_of_closed hs.closed ha)

/-- `lem:as-countermodel`(1) and the final sentence of (2): decode the
least hull, retaining its exact atoms and all specified observations. -/
theorem countermodel (w : CounterexampleWord c φ ψ k) (hφ : ∃ ρ, SatT c ρ φ) :
    ∃ ρ, SatT c ρ φ ∧ configSet c ρ = Hull c φ w.seeds ∧
      (∀ o ∈ w.observations, o.Holds c ρ) ∧
      ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  obtain ⟨ρ, hs, he⟩ := sol_iff_assignment.mp (w.hull_model hφ)
  have ho := w.observations_of_configSet hφ he
  exact ⟨ρ, hs, he, ho, w.observations_no_extension hφ ho⟩

/-- The finite ground bounds `B` corresponding to `O`. -/
def bounds (w : CounterexampleWord c φ ψ k) : List (GroundBound n X) :=
  w.observations.map (Core.Mixed.Observation.bound c)

/-- `lem:as-countermodel`(3): these are exactly the observation pins. -/
theorem bounds_iff (w : CounterexampleWord c φ ψ k) (ρ : X → Tree n) :
    (∀ b ∈ w.bounds, b.Holds c ρ) ↔ ∀ o ∈ w.observations, o.Holds c ρ := by
  simp only [bounds, List.forall_mem_map, observation_bound_mixed]

/-- `lem:as-countermodel`(3), for any class realizing ground bounds. -/
theorem pinned_countermodels_of_realization (w : CounterexampleWord c φ ψ k)
    (hφ : ∃ ρ, SatT c ρ φ) {C : Tree n → Prop} (hC : BoundRealization C c φ) :
    (∃ ρ, (∀ x, C (ρ x)) ∧ SatT c ρ φ ∧ ∀ b ∈ w.bounds, b.Holds c ρ) ∧
      (∀ ρ, (∀ x, C (ρ x)) → SatT c ρ φ →
        (∀ b ∈ w.bounds, b.Holds c ρ) → ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) := by
  obtain ⟨ρ, hs, _, ho, _⟩ := w.countermodel hφ
  exact ⟨hC w.bounds ⟨ρ, hs, (w.bounds_iff ρ).mpr ho⟩,
    fun ρ _ _ hb => w.observations_no_extension hφ ((w.bounds_iff ρ).mp hb)⟩

end CounterexampleWord

/-- The three tree classes: arbitrary, regular and finite trees. -/
inductive CertificateTreeClass where
  | all | regular | finite

/-- Interpret a tree class as a predicate on trees. -/
def CertificateTreeClass.Holds : CertificateTreeClass → Tree n → Prop
  | .all => fun _ => True
  | .regular => RegularTop
  | .finite => FiniteTop

/-- `lem:as-countermodel`(3), for each of the three tree classes. -/
theorem CounterexampleWord.pinned_countermodels {k : CertificateKind}
    (w : CounterexampleWord c φ ψ k) (D : CertificateTreeClass)
    (hφ : SatisfiableIn D.Holds c φ) :
    (∃ ρ, (∀ x, D.Holds (ρ x)) ∧ SatT c ρ φ ∧ ∀ b ∈ w.bounds, b.Holds c ρ) ∧
      (∀ ρ, (∀ x, D.Holds (ρ x)) → SatT c ρ φ →
        (∀ b ∈ w.bounds, b.Holds c ρ) → ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) := by
  have hs : ∃ ρ, SatT c ρ φ := by obtain ⟨ρ, _, hρ⟩ := hφ; exact ⟨ρ, hρ⟩
  apply w.pinned_countermodels_of_realization hs
  cases D with
  | all =>
    rintro B ⟨ρ, hρ, hb⟩
    exact ⟨ρ, fun _ => trivial, hρ, hb⟩
  | regular => exact regular_bound_realization c φ
  | finite => exact finite_bound_realization c φ hφ

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- `lem:as-countermodel`(4): restrict the same countermodel to the original visible
variables, with top-freeness and the tree class preserved. -/
theorem gadget_countermodel {C : Tree n → Prop} (hC : TopFree.HasWitnesses C)
    {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z} (hzs : ∀ z, z ∈ zs)
    (φ₀ : List (LitT n X)) (ψ₀ : List (LitT n (X ⊕ Z)))
    (ρ : X ⊕ X → Tree n) (hρ : ∀ x, C (ρ x))
    (hs : SatT (fun _ => false) ρ (TopFree.gadgetAnte xs φ₀))
    (hne : ¬ ∃ σ, (∀ z, C (σ z)) ∧
      SatT (fun _ => false) (Sum.elim ρ σ) (TopFree.gadgetCons zs ψ₀)) :
    (∀ x, TopFree (ρ (.inl x)) ∧ C (ρ (.inl x))) ∧
      SatT (fun _ => false) (ρ ∘ Sum.inl) φ₀ ∧
      ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ C (σ z)) ∧
        SatT (fun _ => false) (Sum.elim (ρ ∘ Sum.inl) σ) ψ₀ := by
  obtain ⟨hφ, hw⟩ := (TopFree.satT_gadgetAnte hxs φ₀ ρ).mp hs
  refine ⟨fun x => ⟨TopFree.of_isWitness (hw x), hρ _⟩, hφ, ?_⟩
  rintro ⟨σ, hσ, ht⟩
  choose y hyC hy using fun z => hC (σ z) (hσ z).1 (hσ z).2
  apply hne
  refine ⟨Sum.elim σ y, ?_, (TopFree.satT_gadgetCons hzs ψ₀ ρ _).mpr ⟨ht, hy⟩⟩
  rintro (z | z)
  exacts [(hσ z).2, hyC z]

end DeciENSSE
