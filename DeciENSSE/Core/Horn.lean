import DeciENSSE.Core.Basic

/-! # Horn characterization of covariant existential entailment

An atom `(x, w)` says that the tree assigned to `x` has a constructor at `w`.
Tree constraints become unary Horn rules on these atoms: copies, pushes,
pops, and truncations, together with forced roots and forbidden roots.
`assignmentEquiv` identifies tree assignments with prefix-closed atom sets.
`mu_least` characterizes the least solution of a satisfiable system, and
`cl_least` characterizes its least solution containing a live seed.

This is the condition step of the covariant proof. `three_conditions` says
that, for satisfiable antecedent and consequent, existential entailment is
exactly preservation of forced visible atoms (I0), liveness, and visible
consequences of a live seed (II).

The conditions have the same roles as (I0), (U), and (II) in
`Core/Mixed/Conditions`, with constructor atoms replaced there by signed leaf
atoms. Here a seed is live exactly when its closure avoids forbidden roots,
so `CondLive` supplies the unit-obstruction check represented there by (U).
With variance, a seed can also derive opposite signed atoms: its own closure
can collide with itself. The variance proof therefore separates unit and
self-event obstructions to liveness. Its (U) checks forbidden units, while
(I0), (II), and the collision argument exclude inconsistent extensions;
self events also enter the automata tests for live antecedent seeds.

## Main declarations

- `assignmentEquiv`, `sat_iff_sol`: assignments as Horn solutions.
- `Mu`, `Cl`, `Live`, `Hull`: forced atoms, seed closures, liveness, and hulls.
- `mu_least`, `cl_least`: least solutions, with and without a live seed.
- `Projected`, `projected_iff`: extensions characterized by visible Horn data.
- `CondI0`, `CondLive`, `CondII`, `three_conditions`: the entailment criterion.
-/

namespace DeciENSSE.Core

variable {n : ℕ}

/-- A variable paired with a constructor position. -/
abbrev Config (n : ℕ) (V : Type*) := V × List (Fin n)

/-- Constructor positions present in an assignment. -/
def configSet {V : Type*} (ρ : V → BFTree n) : Set (Config n V) :=
  {a | a.2 ∈ (ρ a.1).K}

/-- Each variable component is closed under word prefixes. -/
def PrefixClosed {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ v u w, (v, u ++ w) ∈ S → (v, u) ∈ S

/-- Deleting the last letter preserves membership. -/
def TruncClosed {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ v w c, (v, w ++ [c]) ∈ S → (v, w) ∈ S

/-- Prefix closure is equivalent to closure under single-letter truncation. -/
theorem prefixClosed_iff_truncClosed {V : Type*} {S : Set (Config n V)} :
    PrefixClosed S ↔ TruncClosed S := by
  constructor
  · intro h v w c; exact h v w [c]
  · intro h v u w
    induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton w c ih =>
      intro hw
      exact ih (h v (u ++ w) c (by simpa [List.append_assoc] using hw))

/-- Every tree assignment has a prefix-closed configuration set. -/
theorem configSet_prefixClosed {V : Type*} (ρ : V → BFTree n) :
    PrefixClosed (configSet ρ) := fun v u w => (ρ v).prefix_closed u w

/-- Recover an assignment from a prefix-closed configuration set. -/
def assignmentOf {V : Type*} (S : Set (Config n V)) (h : PrefixClosed S) :
    V → BFTree n := fun v => ⟨{w | (v, w) ∈ S}, h v⟩

/-- Recovering an assignment preserves its configurations. -/
@[simp] theorem configSet_assignmentOf {V : Type*} (S : Set (Config n V))
    (h : PrefixClosed S) : configSet (assignmentOf S h) = S := rfl

/-- Recovering an assignment from its configurations is the identity. -/
@[simp] theorem assignmentOf_configSet {V : Type*} (ρ : V → BFTree n) :
    assignmentOf (configSet ρ) (configSet_prefixClosed ρ) = ρ := rfl

/-- The bijection between tree assignments and prefix-closed configuration sets. -/
def assignmentEquiv (V : Type*) :
    (V → BFTree n) ≃ {S : Set (Config n V) // PrefixClosed S} where
  toFun ρ := ⟨configSet ρ, configSet_prefixClosed ρ⟩
  invFun S := assignmentOf S.val S.property
  left_inv _ := rfl
  right_inv _ := rfl

/-- Top-of-stack rules, indexed by a constructor child. -/
inductive Move {V : Type*} (χ : List (Lit n V)) : Config n V → Config n V → Prop
  | copy {u v w} : Lit.le u v ∈ χ → Move χ (u, w) (v, w)
  | push {a u w} (i : Fin n) : Lit.fle a u ∈ χ →
      Move χ (a i, w) (u, i :: w)
  | pop {u a w} (i : Fin n) : Lit.lef u a ∈ χ →
      Move χ (u, i :: w) (a i, w)

/-- Truncation deletes the bottom (last) letter, not the stack top. -/
inductive Clause {V : Type*} (χ : List (Lit n V)) : Config n V → Config n V → Prop
  | move {a b} : Move χ a b → Clause χ a b
  | trunc (v : V) (w : List (Fin n)) (i : Fin n) : Clause χ (v, w ++ [i]) (v, w)

/-- Constructor lower bounds force their root configurations. -/
def Fact {V : Type*} (χ : List (Lit n V)) : Set (Config n V) :=
  {p | p.2 = [] ∧ ∃ a, Lit.fle a p.1 ∈ χ}

/-- Bottom equations forbid their root configurations. -/
def Neg {V : Type*} (χ : List (Lit n V)) : Set (Config n V) :=
  {p | p.2 = [] ∧ Lit.bot p.1 ∈ χ}

/-- Every Horn clause preserves membership. -/
def Closed {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃a b⦄, Clause χ a b → a ∈ S → b ∈ S

/-- No forbidden root belongs to the configuration set. -/
def Avoids {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃a⦄, a ∈ S → a ∉ Neg χ

/-- Solutions as sets; prefix closure follows from the truncation clauses. -/
structure Sol {V : Type*} (χ : List (Lit n V)) (S : Set (Config n V)) : Prop where
  /-- Membership is preserved by every Horn clause. -/
  closed : Closed χ S
  /-- Every forced root is present. -/
  facts : Fact χ ⊆ S
  /-- Every forbidden root is absent. -/
  avoids : Avoids χ S

variable {V : Type*} {χ : List (Lit n V)}

/-- Closure under Horn clauses includes prefix closure. -/
theorem Closed.prefixClosed {S : Set (Config n V)} (h : Closed χ S) : PrefixClosed S :=
  prefixClosed_iff_truncClosed.mpr (fun v w c => h (.trunc v w c))

/-- Tree satisfaction agrees with the configuration-set Horn semantics. -/
theorem sat_iff_sol (ρ : V → BFTree n) : Sat ρ χ ↔ Sol χ (configSet ρ) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro p q hpq hp
      cases hpq with
      | trunc v w c => exact (ρ v).prefix_closed w [c] hp
      | move hm =>
        cases hm with
        | copy hl => exact h _ hl hp
        | push c hl => exact h _ hl hp
        | pop c hl => exact h _ hl hp
    · rintro ⟨u, w⟩ ⟨rfl, a, hl⟩
      exact h _ hl (BFTree.nil_mem_node _)
    · rintro ⟨u, w⟩ hw ⟨rfl, hl⟩
      change [] ∈ (ρ u).K at hw
      have hb : ρ u = BFTree.bot := h _ hl
      simp [hb] at hw
  · intro h l hl
    cases l with
    | le u v => exact fun _ hw => h.closed (.move (.copy hl)) hw
    | fle a u =>
      intro w hw
      cases w with
      | nil => exact h.facts (show (u, []) ∈ Fact χ from ⟨rfl, a, hl⟩)
      | cons c w => exact h.closed (.move (.push _ hl)) hw
    | lef u a =>
      intro w hw
      cases w with
      | nil => trivial
      | cons c w => exact h.closed (.move (.pop _ hl)) hw
    | bot u =>
      apply BFTree.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact h.avoids (a := (u, [])) ((ρ u).prefix_closed [] w hw) ⟨rfl, hl⟩

/-- Horn solutions are exactly satisfying assignments represented as sets. -/
theorem sol_iff_assignment {S : Set (Config n V)} :
    Sol χ S ↔ ∃ ρ, Sat ρ χ ∧ configSet ρ = S := by
  constructor
  · intro h
    exact ⟨assignmentOf S h.closed.prefixClosed, (sat_iff_sol _).mpr h, rfl⟩
  · rintro ⟨ρ, h, rfl⟩; exact (sat_iff_sol ρ).mp h

/-- Finite derivations, with a reflexive seed and one clause per step. -/
inductive Reach (χ : List (Lit n V)) (a : Config n V) : Config n V → Prop
  | refl : Reach χ a a
  | step {b c} : Reach χ a b → Clause χ b c → Reach χ a c

/-- The configurations reachable from forced roots. -/
def Mu (χ : List (Lit n V)) : Set (Config n V) :=
  {b | ∃ a ∈ Fact χ, Reach χ a b}

/-- The least fact-containing closure of one configuration. -/
def Cl (χ : List (Lit n V)) (a : Config n V) : Set (Config n V) :=
  Mu χ ∪ {b | Reach χ a b}

/-- Semantic liveness, meaningful even for an inconsistent system. -/
def Live (χ : List (Lit n V)) : Set (Config n V) :=
  {a | ∃ S, Sol χ S ∧ a ∈ S}

/-- The least fact-containing, clause-closed extension of a seed set. -/
def Hull (χ : List (Lit n V)) (A : Set (Config n V)) : Set (Config n V) :=
  Mu χ ∪ {b | ∃ a ∈ A, Reach χ a b}

/-- Reachability preserves membership in a closed set. -/
theorem Reach.mem_of_closed {a b : Config n V} {S : Set (Config n V)}
    (h : Reach χ a b) (hc : Closed χ S) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | step _ hs ih => exact hc hs ih

/-- The configurations reachable from one seed form a closed set. -/
theorem reach_closed (a : Config n V) : Closed χ {b | Reach χ a b} :=
  by
  intro b c h hb
  exact Reach.step hb h

/-- Compose two finite Horn derivations. -/
theorem Reach.trans {a b c : Config n V} (h : Reach χ a b) (h' : Reach χ b c) :
    Reach χ a c := h'.mem_of_closed (reach_closed a) h

/-- The least fact closure is closed under every Horn clause. -/
theorem mu_closed : Closed χ (Mu χ) := by
  rintro a b h ⟨s, hs, hr⟩
  exact ⟨s, hs, .step hr h⟩

/-- Every forced root belongs to the least fact closure. -/
theorem facts_subset_mu : Fact χ ⊆ Mu χ := fun a ha => ⟨a, ha, .refl⟩

/-- Every closed set containing the facts contains their least closure. -/
theorem mu_subset {S : Set (Config n V)} (hc : Closed χ S) (hf : Fact χ ⊆ S) :
    Mu χ ⊆ S := by
  rintro b ⟨a, ha, hr⟩
  exact hr.mem_of_closed hc (hf ha)

/-- The Horn hull of any seed set is closed. -/
theorem hull_closed (A : Set (Config n V)) : Closed χ (Hull χ A) := by
  intro a b h ha
  rcases ha with ha | ⟨s, hs, hr⟩
  · exact Or.inl (mu_closed h ha)
  · exact Or.inr ⟨s, hs, .step hr h⟩

/-- The Horn hull contains both the facts and its seeds. -/
theorem hull_contains (A : Set (Config n V)) : Fact χ ∪ A ⊆ Hull χ A := by
  intro a ha
  rcases ha with ha | ha
  · exact Or.inl (facts_subset_mu ha)
  · exact Or.inr ⟨a, ha, .refl⟩

/-- Least Horn hull, including both closure and minimality. -/
theorem hull_least (A : Set (Config n V)) :
    Closed χ (Hull χ A) ∧ Fact χ ∪ A ⊆ Hull χ A ∧
      ∀ S, Closed χ S → Fact χ ∪ A ⊆ S → Hull χ A ⊆ S := by
  refine ⟨hull_closed A, hull_contains A, ?_⟩
  intro S hc hf b hb
  rcases hb with hb | ⟨a, ha, hr⟩
  · exact mu_subset hc (fun _ h => hf (Or.inl h)) hb
  · exact hr.mem_of_closed hc (hf (Or.inr ha))

/-- A singleton closure is closed under Horn clauses. -/
theorem cl_closed (a : Config n V) : Closed χ (Cl χ a) := by
  intro b c h hb
  rcases hb with hb | hb
  · exact Or.inl (mu_closed h hb)
  · exact Or.inr (Reach.step hb h)

/-- A configuration belongs to its own closure. -/
theorem mem_cl (a : Config n V) : a ∈ Cl χ a := Or.inr .refl

/-- Every solution contains the least fact closure. -/
theorem Sol.mu_subset {S : Set (Config n V)} (h : Sol χ S) : Mu χ ⊆ S :=
  DeciENSSE.Core.mu_subset h.closed h.facts

/-- A solution containing a seed contains its singleton closure. -/
theorem Sol.cl_subset {S : Set (Config n V)} (h : Sol χ S)
    {a : Config n V} (ha : a ∈ S) : Cl χ a ⊆ S := by
  intro b hb
  rcases hb with hb | hb
  · exact h.mu_subset hb
  · exact hb.mem_of_closed h.closed ha

/-- Satisfiability is equivalent to consistency of the least fact closure. -/
theorem satisfiable_iff_mu_avoids : (∃ ρ, Sat ρ χ) ↔ Avoids χ (Mu χ) := by
  constructor
  · rintro ⟨ρ, hρ⟩ a ha
    have h := (sat_iff_sol ρ).mp hρ
    exact h.avoids (h.mu_subset ha)
  · intro h
    exact (sol_iff_assignment.mp ⟨mu_closed, facts_subset_mu, h⟩).imp
      (fun _ h => h.1)

/-- A satisfiable system has its least fact closure as a solution. -/
theorem mu_sol (h : ∃ ρ, Sat ρ χ) : Sol χ (Mu χ) :=
  ⟨mu_closed, facts_subset_mu, satisfiable_iff_mu_avoids.mp h⟩

/-- The least solution of a satisfiable Horn system. -/
theorem mu_least (h : ∃ ρ, Sat ρ χ) :
    Sol χ (Mu χ) ∧ ∀ S, Sol χ S → Mu χ ⊆ S :=
  ⟨mu_sol h, fun _ hs => hs.mu_subset⟩

/-- The closure of a live seed is a solution. -/
theorem cl_sol {a : Config n V} (ha : a ∈ Live χ) : Sol χ (Cl χ a) := by
  obtain ⟨S, hs, ha⟩ := ha
  exact ⟨cl_closed a, fun _ h => Or.inl (facts_subset_mu h),
    fun _ h => hs.avoids (hs.cl_subset ha h)⟩

/-- The least solution containing a live seed. -/
theorem cl_least {a : Config n V} (ha : a ∈ Live χ) :
    Sol χ (Cl χ a) ∧ a ∈ Cl χ a ∧
      ∀ S, Sol χ S → a ∈ S → Cl χ a ⊆ S :=
  ⟨cl_sol ha, mem_cl a, fun _ hs ha => hs.cl_subset ha⟩

/-- A seed is live exactly when its closure avoids forbidden roots. -/
theorem live_iff_cl_avoids (_h : ∃ ρ, Sat ρ χ) (a : Config n V) :
    a ∈ Live χ ↔ Avoids χ (Cl χ a) := by
  constructor
  · intro ha; exact (cl_sol ha).avoids
  · intro ha
    exact ⟨Cl χ a, ⟨cl_closed a, fun _ h => Or.inl (facts_subset_mu h), ha⟩, mem_cl a⟩

/-- Liveness is equivalent to avoiding forbidden roots along reachable paths. -/
theorem live_iff_reach_avoids (h : ∃ ρ, Sat ρ χ) (a : Config n V) :
    a ∈ Live χ ↔ Avoids χ {b | Reach χ a b} := by
  rw [live_iff_cl_avoids h]
  constructor
  · intro hc b hb; exact hc (Or.inr hb)
  · intro hr b hb
    rcases hb with hb | hb
    · exact (satisfiable_iff_mu_avoids.mp h) hb
    · exact hr hb

/-- Closure under unions of nonempty subfamilies. -/
theorem sol_sUnion {F : Set (Set (Config n V))} (hne : F.Nonempty)
    (hF : ∀ S ∈ F, Sol χ S) : Sol χ (⋃₀ F) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b h ⟨S, hs, ha⟩
    exact ⟨S, hs, (hF S hs).closed h ha⟩
  · obtain ⟨S, hs⟩ := hne
    exact fun a ha => ⟨S, hs, (hF S hs).facts ha⟩
  · rintro a ⟨S, hs, ha⟩
    exact (hF S hs).avoids ha

/-- Closure under intersections of nonempty subfamilies. -/
theorem sol_sInter {F : Set (Set (Config n V))} (hne : F.Nonempty)
    (hF : ∀ S ∈ F, Sol χ S) : Sol χ (⋂₀ F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h ha S hs
    exact (hF S hs).closed h (ha S hs)
  · intro a ha S hs
    exact (hF S hs).facts ha
  · intro a ha
    obtain ⟨S, hs⟩ := hne
    exact (hF S hs).avoids (ha S hs)

/-! The general set-family characterization by least, greatest, and pointed closures. -/

namespace HornFamily
variable {Ω : Type*}

/-- Nonempty subfamilies are closed under unions and intersections. -/
def LatticeClosed (F : Set (Set Ω)) : Prop :=
  ∀ G : Set (Set Ω), G.Nonempty → G ⊆ F → ⋃₀ G ∈ F ∧ ⋂₀ G ∈ F

/-- The intersection of family members containing the given point. -/
def PointCl (F : Set (Set Ω)) (a : Ω) : Set Ω := ⋂₀ {S ∈ F | a ∈ S}

/-- A point belongs to its own family closure. -/
theorem mem_pointCl (F : Set (Set Ω)) (a : Ω) : a ∈ PointCl F a :=
  fun _ h => h.2

/-- A family member containing a point contains its closure. -/
theorem pointCl_subset {F : Set (Set Ω)} {S : Set Ω} (hs : S ∈ F)
    {a : Ω} (ha : a ∈ S) : PointCl F a ⊆ S := fun _ h => h S ⟨hs, ha⟩

/-- The intersection and union of a nonempty closed family are members. -/
theorem data_mem {F : Set (Set Ω)} (hne : F.Nonempty) (hc : LatticeClosed F) :
    ⋂₀ F ∈ F ∧ ⋃₀ F ∈ F ∧ ∀ a ∈ ⋃₀ F, PointCl F a ∈ F := by
  refine ⟨(hc F hne (Set.Subset.refl _)).2,
    (hc F hne (Set.Subset.refl _)).1, ?_⟩
  rintro a ⟨S, hs, ha⟩
  exact (hc {T ∈ F | a ∈ T} ⟨S, hs, ha⟩ (fun _ h => h.1)).2

/-- Characterize a closed family by its least, greatest, and pointed closures. -/
theorem alexandrov {F : Set (Set Ω)} (hne : F.Nonempty) (hc : LatticeClosed F)
    (S : Set Ω) :
    S ∈ F ↔ ⋂₀ F ⊆ S ∧ S ⊆ ⋃₀ F ∧ ∀ a ∈ S, PointCl F a ⊆ S := by
  constructor
  · intro hs
    exact ⟨fun _ h => h S hs, fun a ha => ⟨S, hs, ha⟩,
      fun _ ha => pointCl_subset hs ha⟩
  · rintro ⟨hmin, hmax, hcl⟩
    let G : Set (Set Ω) := {T | T = ⋂₀ F ∨ ∃ a ∈ S, T = PointCl F a}
    have hG : G ⊆ F := by
      rintro T (rfl | ⟨a, ha, rfl⟩)
      · exact (data_mem hne hc).1
      · exact (data_mem hne hc).2.2 a (hmax ha)
    have heq : ⋃₀ G = S := by
      apply Set.Subset.antisymm
      · rintro b ⟨T, (rfl | ⟨a, ha, rfl⟩), hb⟩
        · exact hmin hb
        · exact hcl a ha hb
      · intro a ha
        exact ⟨PointCl F a, Or.inr ⟨a, ha, rfl⟩, mem_pointCl F a⟩
    rw [← heq]
    exact (hc G ⟨⋂₀ F, Or.inl rfl⟩ hG).1

end HornFamily

variable {X Z : Type*}

/-- Visible configurations embedded into the disjoint union of variables. -/
def visible (a : Config n X) : Config n (X ⊕ Z) := (.inl a.1, a.2)

/-- Restriction is an inverse image, so its result has visible variable type. -/
def restrict (S : Set (Config n (X ⊕ Z))) : Set (Config n X) :=
  {a | visible a ∈ S}

/-- Visible restrictions of solutions of the consequent. -/
def Projected (ψ : List (Lit n (X ⊕ Z))) : Set (Set (Config n X)) :=
  {S | ∃ T, Sol ψ T ∧ restrict T = S}

/-- Projected membership means existence of a hidden-variable extension. -/
theorem projected_configSet (ρ : X → BFTree n) (ψ : List (Lit n (X ⊕ Z))) :
    configSet ρ ∈ Projected ψ ↔ ∃ σ, Sat (Sum.elim ρ σ) ψ := by
  constructor
  · rintro ⟨T, ht, heq⟩
    obtain ⟨τ, hτ, rfl⟩ := sol_iff_assignment.mp ht
    have hv : ∀ x, τ (.inl x) = ρ x := by
      intro x
      apply BFTree.ext
      exact congrArg (fun S => {w | (x, w) ∈ S}) heq
    refine ⟨fun z => τ (.inr z), ?_⟩
    have he : Sum.elim ρ (fun z => τ (.inr z)) = τ := by
      funext v
      cases v with
      | inl x => exact (hv x).symm
      | inr z => rfl
    rw [he]; exact hτ
  · rintro ⟨σ, hσ⟩
    exact ⟨configSet (Sum.elim ρ σ), (sat_iff_sol _).mp hσ, rfl⟩

/-- Existential entailment is inclusion of `Sol` in `Projected`. -/
theorem existsEntails_iff_sol_subset (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsTopFree φ ψ ↔ ∀ S, Sol φ S → S ∈ Projected ψ := by
  constructor
  · intro h S hs
    obtain ⟨ρ, hρ, rfl⟩ := sol_iff_assignment.mp hs
    obtain ⟨σ, _, hσ⟩ := h ρ (fun _ => trivial) hρ
    exact (projected_configSet ρ ψ).mpr ⟨σ, hσ⟩
  · intro h ρ _ hρ
    obtain ⟨σ, hσ⟩ := (projected_configSet ρ ψ).mp (h _ ((sat_iff_sol _).mp hρ))
    exact ⟨σ, fun _ => trivial, hσ⟩

/-- Restriction preserves nonempty lattice closure, including projected families. -/
theorem projected_latticeClosed (ψ : List (Lit n (X ⊕ Z))) :
    HornFamily.LatticeClosed (Projected ψ) := by
  classical
  intro F hne hF
  let G : Set (Set (Config n (X ⊕ Z))) := {T | Sol ψ T ∧ restrict T ∈ F}
  have hG : G.Nonempty := by
    obtain ⟨S, hs⟩ := hne
    obtain ⟨T, ht, rfl⟩ := hF hs
    exact ⟨T, ht, hs⟩
  constructor
  · refine ⟨⋃₀ G, sol_sUnion hG (fun _ h => h.1), ?_⟩
    apply Set.Subset.antisymm
    · rintro a ⟨T, ⟨ht, hf⟩, ha⟩
      exact ⟨restrict T, hf, ha⟩
    · rintro a ⟨S, hs, ha⟩
      obtain ⟨T, ht, rfl⟩ := hF hs
      exact ⟨T, ⟨ht, hs⟩, ha⟩
  · refine ⟨⋂₀ G, sol_sInter hG (fun _ h => h.1), ?_⟩
    apply Set.Subset.antisymm
    · intro a ha S hs
      obtain ⟨T, ht, rfl⟩ := hF hs
      exact ha T ⟨ht, hs⟩
    · intro a ha T ht
      exact ha (restrict T) ht.2

/-- Projected Horn data, nonemptiness. -/
theorem projected_nonempty {ψ : List (Lit n (X ⊕ Z))} (h : ∃ ρ, Sat ρ ψ) :
    (Projected ψ).Nonempty := ⟨restrict (Mu ψ), Mu ψ, mu_sol h, rfl⟩

/-- Projected Horn data, least member. -/
theorem projected_sInter {ψ : List (Lit n (X ⊕ Z))} (h : ∃ ρ, Sat ρ ψ) :
    ⋂₀ Projected ψ = restrict (Mu ψ) := by
  apply Set.Subset.antisymm
  · intro a ha
    exact ha (restrict (Mu ψ)) ⟨Mu ψ, mu_sol h, rfl⟩
  · rintro a ha S ⟨T, ht, rfl⟩
    exact ht.mu_subset ha

/-- Projected Horn data, greatest member (in fact valid without satisfiability). -/
theorem projected_sUnion (ψ : List (Lit n (X ⊕ Z))) :
    ⋃₀ Projected ψ = restrict (Live ψ) := by
  apply Set.Subset.antisymm
  · rintro a ⟨S, ⟨T, ht, rfl⟩, ha⟩
    exact ⟨T, ht, ha⟩
  · rintro a ⟨T, ht, ha⟩
    exact ⟨restrict T, ⟨T, ht, rfl⟩, ha⟩

/-- Projected Horn data, specialization closure of a live visible point. -/
theorem projected_pointCl {ψ : List (Lit n (X ⊕ Z))} {a : Config n X}
    (ha : visible a ∈ Live ψ) :
    HornFamily.PointCl (Projected ψ) a = restrict (Cl ψ (visible a)) := by
  apply Set.Subset.antisymm
  · intro b hb
    exact hb (restrict (Cl ψ (visible a)))
      ⟨⟨Cl ψ (visible a), cl_sol ha, rfl⟩, mem_cl (visible a)⟩
  · rintro b hb S ⟨⟨T, ht, rfl⟩, ha⟩
    exact ht.cl_subset ha hb

/-- Projected membership in the three Horn data. -/
theorem projected_iff {ψ : List (Lit n (X ⊕ Z))} (h : ∃ ρ, Sat ρ ψ)
    (S : Set (Config n X)) :
    S ∈ Projected ψ ↔ restrict (Mu ψ) ⊆ S ∧ S ⊆ restrict (Live ψ) ∧
      ∀ a ∈ S, restrict (Cl ψ (visible a)) ⊆ S := by
  rw [HornFamily.alexandrov (projected_nonempty h) (projected_latticeClosed ψ),
    projected_sInter h, projected_sUnion]
  constructor
  · rintro ⟨hm, hl, hc⟩
    refine ⟨hm, hl, fun a ha => ?_⟩
    rw [← projected_pointCl (hl ha)]
    exact hc a ha
  · rintro ⟨hm, hl, hc⟩
    refine ⟨hm, hl, fun a ha => ?_⟩
    rw [projected_pointCl (hl ha)]
    exact hc a ha

/-- `CondI0`: every visible fact consequence of ψ is forced by φ. -/
def CondI0 (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  restrict (Mu ψ) ⊆ Mu φ

/-- `CondLive`: every φ-live configuration is ψ-live. -/
def CondLive (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  Live φ ⊆ restrict (Live ψ)

/-- `CondII`: visible ψ-reachability from a live point lies in its φ-closure. -/
def CondII (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) : Prop :=
  ∀ a ∈ Live φ, restrict {b | Reach ψ (visible a) b} ⊆ Cl φ a

/-- The closure formulation equivalent to `CondII`, assuming `CondI0`. -/
theorem condII_iff_cl {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    (hi : CondI0 φ ψ) : CondII φ ψ ↔
      ∀ a ∈ Live φ, restrict (Cl ψ (visible a)) ⊆ Cl φ a := by
  constructor
  · intro h a ha b hb
    rcases hb with hb | hb
    · exact Or.inl (hi hb)
    · exact h a ha hb
  · intro h a ha b hb
    exact h a ha (Or.inr hb)

/-- Existential entailment, the vacuous antecedent case. -/
theorem existsEntails_of_unsat {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    (hφ : ¬ ∃ ρ, Sat ρ φ) : ExistsEntailsTopFree φ ψ := by
  intro ρ _ hρ
  exact (hφ ⟨ρ, hρ⟩).elim

/-- Existential entailment in reachability form. -/
theorem three_conditions {φ : List (Lit n X)} {ψ : List (Lit n (X ⊕ Z))}
    (hφ : ∃ ρ, Sat ρ φ) (hψ : ∃ ρ, Sat ρ ψ) :
    ExistsEntailsTopFree φ ψ ↔ CondI0 φ ψ ∧ CondLive φ ψ ∧ CondII φ ψ := by
  rw [existsEntails_iff_sol_subset]
  constructor
  · intro he
    have hmin := (projected_iff hψ (Mu φ)).mp (he _ (mu_sol hφ))
    refine ⟨hmin.1, ?_, ?_⟩
    · intro a ha
      have hc := (projected_iff hψ (Cl φ a)).mp (he _ (cl_sol ha))
      exact hc.2.1 (mem_cl a)
    · intro a ha b hb
      have hc := (projected_iff hψ (Cl φ a)).mp (he _ (cl_sol ha))
      exact hc.2.2 a (mem_cl a) (Or.inr hb)
  · rintro ⟨hi, hii, hiii⟩ S hs
    apply (projected_iff hψ S).mpr
    refine ⟨fun _ h => hs.mu_subset (hi h), ?_, ?_⟩
    · intro a ha
      exact hii ⟨S, hs, ha⟩
    · intro a ha b hb
      exact hs.cl_subset ha ((condII_iff_cl hi).mp hiii a ⟨S, hs, ha⟩ hb)

end DeciENSSE.Core
