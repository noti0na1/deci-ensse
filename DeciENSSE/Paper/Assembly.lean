import DeciENSSE.Counterexamples
import DeciENSSE.Plain

/-! # Paper contract: The Main Theorem

Contract entries for the section *The Main Theorem* (`sec:as`): counterexample words, the
main theorem, countermodels, the counterexample bounds and plain entailment.

Only library results and logical packaging are used below. Flat systems are lists of core
literals over finite variable types `X` and `X ⊕ Z`; `v` and `s` are spelled out as
`Fintype.card X` and `Fintype.card X + Fintype.card Z`. The three tree classes are
`CertificateTreeClass`. Over `{⊥, f}` with `f` covariant, systems are read at the covariant
variance with top-free values, and the gadget pair `(φ♮, ψ♮)` is `TopFree.gadgetAnte` and
`TopFree.gadgetCons` over complete lists of the visible and the hidden variables.
Counterexample words are `CounterexampleWord`, indexed by their kind, with the sets `A` and
`O` of `lem:as-countermodel` as `CounterexampleWord.seeds` and
`CounterexampleWord.observations`. Decidability is a computable definition built from the
public deciders.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Core.Mixed Core.Words Bounds

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-! ## Counterexample words -/

/-- **Definition (Counterexample words)**, `def:as-certificate`(1).
Form: Words are the type CounterexampleWord with a kind index; the entry characterizes the (I0)-words of each length L. The type does not assume the systems satisfiable.
-/
theorem def_as_certificate_1 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .conditionI, w.length = L) ↔
      ∃ q : X × Bool, ∃ w : List (Fin n), w.length = L ∧
        (Sum.inl q.1, q.2, w) ∈ Mu c ψ ∧ (q.1, q.2, w) ∉ Mu c φ :=
  CounterexampleWord.exists_conditionI_iff L

/-- **Definition (Counterexample words)**, `def:as-certificate`(2).
Form: Words are the type CounterexampleWord with a kind index; the entry characterizes the (U)-words of each length L. The type and characterization do not assume the systems satisfiable.
-/
theorem def_as_certificate_2 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .conditionU, w.length = L) ↔
      ∃ p : X × Bool, ∃ w : List (Fin n), w.length = L ∧
        Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w :=
  CounterexampleWord.exists_conditionU_iff L

/-- **Definition (Counterexample words)**, `def:as-certificate`(3).
Form: Words are the type CounterexampleWord with a kind index; the entry characterizes the hole words of each length L and includes the length |u| + |t| + 1 of the separator word u#t. The type and characterization do not assume the systems satisfiable.
-/
theorem def_as_certificate_3 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .hole, w.length = L) ↔
      CondU c φ ψ ∧ ∃ p q : X × Bool, ∃ u t : List (Fin n),
        u.length + t.length + 1 = L ∧ (extractSelf c φ ψ p q).IsHole u t :=
  CounterexampleWord.exists_hole_iff L

/-! ## The main theorem -/

/-- **Theorem (Main theorem)**, `thm:as-main`(1).
Form: Decidability is a computable triple of the public deciders, for arbitrary, regular and finite trees, on flat systems over finite ordinals; expressions are decided by decideExistsEntailsTerm and its variants (thm_intro_main).
-/
def thm_as_main_1 {k h : ℕ} (c : Fin n → Bool) (φ : EConstraint n k)
    (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntails c φ ψ) × Decidable (ExistsEntailsReg c φ ψ) ×
      Decidable (ExistsEntailsFin c φ ψ) :=
  ⟨DeciENSSE.decideExistsEntails c φ ψ, DeciENSSE.decideExistsEntailsReg c φ ψ,
    DeciENSSE.decideExistsEntailsFin c φ ψ⟩

/-- **Theorem (Main theorem)**, `thm:as-main`(2).
Form: Decidability is a computable triple of the public deciders for the bottom-constructor signature with f covariant, over top-free arbitrary, regular and finite trees, on flat systems over finite ordinals.
-/
def thm_as_main_2 {k h : ℕ} (φ : BFConstraint n k) (ψ : BFConstraint n (k + h)) :
    Decidable (ExistsEntailsTopFree φ ψ) × Decidable (ExistsEntailsTopFreeReg φ ψ) ×
      Decidable (ExistsEntailsTopFreeFin φ ψ) :=
  ⟨DeciENSSE.decideExistsEntailsTopFree φ ψ, DeciENSSE.decideExistsEntailsTopFreeReg φ ψ,
    DeciENSSE.decideExistsEntailsTopFreeFin φ ψ⟩

/-- **Theorem (Main theorem)**, `thm:as-main`(3).
Form: D ranges over the three tree classes; the observations of a word are a list of signed leaf atoms. Independence of n and c is the form of the bound.
-/
theorem thm_as_main_3 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (D : CertificateTreeClass) (hφ : SatisfiableIn D.Holds c φ)
    (hψ : SatisfiableIn D.Holds c ψ) (h : ¬ ExistsEntailsTIn D.Holds c φ ψ) :
    ((∃ k, ∃ w : CounterexampleWord c φ ψ k,
        w.length ≤ E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (22 * (Fintype.card X + Fintype.card Z) + 15)) ∧
    ∀ k (w : CounterexampleWord c φ ψ k), w.observations.length ≤ 2 ∧
      (∃ ρ, (∀ x, D.Holds (ρ x)) ∧ SatT c ρ φ ∧ ∀ o ∈ w.observations, o.Holds c ρ) ∧
      ∀ ρ, (∀ x, D.Holds (ρ x)) → SatT c ρ φ → (∀ o ∈ w.observations, o.Holds c ρ) →
        ¬ ∃ σ, (∀ z, D.Holds (σ z)) ∧ SatT c (Sum.elim ρ σ) ψ := by
  refine ⟨exists_short_counterexampleWord D hφ hψ h, fun _ w => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := w.countermodels_in D hφ
  exact ⟨h₁, h₂, fun ρ _ _ ho ⟨σ, _, hσ⟩ => h₃ ρ ho ⟨σ, hσ⟩⟩

/-- **Theorem (Main theorem)**, `thm:as-main`(4).
Form: Systems over the bottom-constructor signature are flat systems read at the covariant variance with top-free values in D; the gadget pair is gadgetAnte and gadgetCons over complete lists xs and zs, with the visible carrier Sum X X and the hidden carrier Sum Z Z.
-/
theorem thm_as_main_4 (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (D : CertificateTreeClass) {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z}
    (hzs : ∀ z, z ∈ zs)
    (hφ : SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ)
    (hψ : SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) ψ)
    (h : ¬ ExistsEntailsTIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ ψ) :
    ((∃ k, ∃ w : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
        (TopFree.gadgetCons zs ψ) k,
        w.length ≤ E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (44 * (Fintype.card X + Fintype.card Z) + 15)) ∧
    ∀ k (_ : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
        (TopFree.gadgetCons zs ψ) k),
      ∃ ρ : X → Tree n, (∀ x, TopFree (ρ x) ∧ D.Holds (ρ x)) ∧ SatT (fun _ => false) ρ φ ∧
        ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
          SatT (fun _ => false) (Sum.elim ρ σ) ψ :=
  ⟨exists_short_counterexampleWord_gadget D hxs hzs hφ hψ h,
    fun _ w => (w.gadget_countermodels hxs hzs D hφ).1⟩

/-! ## Countermodels -/

/-- **Lemma (Countermodels)**, `lem:as-countermodel`(1).
Form: A and O are CounterexampleWord.seeds and observations; mu_phi and Cl_phi are by definition the hulls of the empty set and of a singleton, and the decoding rho_A has the atom set H_phi(A). The satisfiability of psi is not needed.
-/
theorem lem_as_countermodel_1 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (hφ : ∃ ρ, SatT c ρ φ) :
    (∀ (q : X × Bool) (w : List (Fin n)) (hf : (Sum.inl q.1, q.2, w) ∈ Mu c ψ)
        (hn : (q.1, q.2, w) ∉ Mu c φ),
      Hull c φ (CounterexampleWord.ofI q w hf hn).seeds = Mu c φ) ∧
    (∀ (p : X × Bool) (w : List (Fin n)) (hl : Live c φ (p.1, p.2, w)) (hd : DeadU c ψ p w),
      Hull c φ (CounterexampleWord.ofU p w hl hd).seeds = Cl c φ (p.1, p.2, w)) ∧
    (∀ (p q : X × Bool) (u t : List (Fin n)) (hU : CondU c φ ψ)
        (hh : (extractSelf c φ ψ p q).IsHole u t),
      Hull c φ (CounterexampleWord.ofHole p q u t hU hh).seeds = Cl c φ (p.1, p.2, t)) ∧
    ∀ k (w : CounterexampleWord c φ ψ k), Sol c φ (Hull c φ w.seeds) ∧
      ∃ ρ, SatT c ρ φ ∧ configSet c ρ = Hull c φ w.seeds ∧
        ∀ o ∈ w.observations, o.Holds c ρ := by
  refine ⟨CounterexampleWord.hull_ofI, CounterexampleWord.hull_ofU,
    CounterexampleWord.hull_ofHole, fun _ w => ⟨w.hull_model hφ, ?_⟩⟩
  obtain ⟨ρ, hs, he, ho, -⟩ := w.countermodel hφ
  exact ⟨ρ, hs, he, ho⟩

/-- **Lemma (Countermodels)**, `lem:as-countermodel`(2).
Form: The satisfiability of psi is not needed; rho_A is identified by its atom set H_phi(A).
-/
theorem lem_as_countermodel_2 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (hφ : ∃ ρ, SatT c ρ φ) {k : CertificateKind}
    (w : CounterexampleWord c φ ψ k) :
    (∀ ρ : X → Tree n, (∀ o ∈ w.observations, o.Holds c ρ) →
      ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) ∧
    ∃ ρ, SatT c ρ φ ∧ configSet c ρ = Hull c φ w.seeds ∧ ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  refine ⟨fun _ ho => w.observations_no_extension hφ ho, ?_⟩
  obtain ⟨ρ, hs, he, -, hn⟩ := w.countermodel hφ
  exact ⟨ρ, hs, he, hn⟩

/-- **Lemma (Countermodels)**, `lem:as-countermodel`(3).
Form: B is the list CounterexampleWord.bounds of ground bounds with finite-term trees; the union of phi and B is SatT together with the bounds; no extension exists even with arbitrary values. The satisfiability of psi is not needed.
-/
theorem lem_as_countermodel_3 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) {k : CertificateKind} (w : CounterexampleWord c φ ψ k)
    (D : CertificateTreeClass) (hφ : SatisfiableIn D.Holds c φ) :
    (∀ ρ : X → Tree n, (∀ b ∈ w.bounds, b.Holds c ρ) ↔ ∀ o ∈ w.observations, o.Holds c ρ) ∧
    (∃ ρ, (∀ x, D.Holds (ρ x)) ∧ SatT c ρ φ ∧ ∀ b ∈ w.bounds, b.Holds c ρ) ∧
    ∀ ρ, (∀ x, D.Holds (ρ x)) → SatT c ρ φ → (∀ b ∈ w.bounds, b.Holds c ρ) →
      ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ :=
  ⟨w.bounds_iff, w.pinned_countermodels D hφ⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- **Lemma (Countermodels)**, `lem:as-countermodel`(4).
Form: Systems over the bottom-constructor signature are read at the covariant variance with top-free values; the gadget pair is gadgetAnte and gadgetCons over complete lists xs and zs, and the restriction is the composition of rho with Sum.inl. No counterexample word or satisfiability assumption on the gadget consequent is required; the input literals may use the full signature, interpreted on top-free values.
-/
theorem lem_as_countermodel_4 {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z}
    (hzs : ∀ z, z ∈ zs) (φ₀ : List (LitT n X)) (ψ₀ : List (LitT n (X ⊕ Z)))
    (D : CertificateTreeClass) (ρ : X ⊕ X → Tree n) (hρ : ∀ x, D.Holds (ρ x))
    (hs : SatT (fun _ => false) ρ (TopFree.gadgetAnte xs φ₀))
    (hne : ¬ ∃ σ, (∀ z, D.Holds (σ z)) ∧
      SatT (fun _ => false) (Sum.elim ρ σ) (TopFree.gadgetCons zs ψ₀)) :
    (∀ x, TopFree (ρ (.inl x)) ∧ D.Holds (ρ (.inl x))) ∧
      SatT (fun _ => false) (ρ ∘ Sum.inl) φ₀ ∧
      ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
        SatT (fun _ => false) (Sum.elim (ρ ∘ Sum.inl) σ) ψ₀ :=
  gadget_countermodel D.hasWitnesses hxs hzs φ₀ ψ₀ ρ hρ hs hne

/-! ## Counterexample bounds -/

/-- **Proposition (Counterexample bounds)**, `prop:as-bounds`(1).
Form: No satisfiability hypothesis is needed.
-/
theorem prop_as_bounds_1 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (h : ¬ CondI0 c φ ψ) :
    ∃ w : CounterexampleWord c φ ψ .conditionI,
      w.length < 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 2) :=
  CounterexampleWord.exists_short_conditionI h

/-- **Proposition (Counterexample bounds)**, `prop:as-bounds`(2).
Form: holeBound(N_U, d_{N_U}) is holeLengthBound at the N_U states of the unit reader, the type TargetState X Z; the satisfiability of psi is not needed.
-/
theorem prop_as_bounds_2 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (hφ : ∃ ρ, SatT c ρ φ) (h : ¬ CondU c φ ψ) :
    (∃ w : CounterexampleWord c φ ψ .conditionU,
      w.length ≤ DeciNSSE.RejectedTail.holeLengthBound (Fintype.card (TargetState X Z))) ∧
      DeciNSSE.RejectedTail.holeLengthBound (Fintype.card (TargetState X Z)) ≤
        E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) :=
  CounterexampleWord.exists_short_conditionU hφ h

/-- **Proposition (Counterexample bounds)**, `prop:as-bounds`(3).
Form: (I0) and the satisfiability of psi are not needed; Lnm and Len-sharp are extractedBoundSelf at the state counts of extractSelf, and condI0Bound is the bound of (1). This item includes the closing claims; that the mortal bound is the largest is proved for the closed forms, E3(10v+10s+17) ≤ E3(10v+12s+15), and every exact bound is at most the mortal closed form.
-/
theorem prop_as_bounds_3 (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ((∃ ρ, SatT c ρ φ) → CondU c φ ψ → ¬ CondII c φ ψ →
      ∃ p q : X × Bool, ∃ u t : List (Fin n), (extractSelf c φ ψ p q).IsHole u t ∧
        (u.length + t.length ≤ extractedBoundSelf pumpHoleBound X Z ∨
          ((extractSelf c φ ψ p q).IsMortalHole u t ∧
            u.length + t.length + 1 ≤ extractedBoundSelf Mortal.mortalHoleBound X Z ∧
            extractedBoundSelf Mortal.mortalHoleBound X Z ≤
              E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15)))) ∧
    extractedBoundSelf pumpHoleBound X Z ≤
      54 * 2 ^ (6 * Fintype.card X + 6 * (Fintype.card X + Fintype.card Z) + 1) ∧
    (0 < Fintype.card X →
      condI0Bound X Z ≤
          E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
        DeciNSSE.RejectedTail.holeLengthBound (Fintype.card (TargetState X Z)) ≤
          E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
        extractedBoundSelf pumpHoleBound X Z + 1 ≤
          E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
        extractedBoundSelf Mortal.mortalHoleBound X Z ≤
          E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
        E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) ≤
          E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ∧
        E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
          E3 (22 * (Fintype.card X + Fintype.card Z) + 15)) ∧
    (IsEmpty X → ∀ k, IsEmpty (CounterexampleWord c φ ψ k)) :=
  ⟨exists_short_extracted_hole c φ ψ, extracted_pumpHoleBound_le.1,
    counterexampleBounds_le, fun _ _ => CounterexampleWord.isEmpty⟩

/-! ## Plain entailment -/

/-- **Corollary (Plain entailment)**, `cor:as-plain`.
Form: Plain entailment is existential entailment with no hidden variables and the consequent query x y (bfQuery over the bottom-constructor signature). Decidability is a computable pair of triples of the public deciders; the two equivalences are the propositional component, with Sat_fin(phi) a solution by finite terms.
-/
def cor_as_plain {k : ℕ} (c : Fin n → Bool) (φ : EConstraint n k) (φ' : BFConstraint n k)
    (x y : V k) :
    (Decidable (ExistsEntails (h := 0) c φ (query x y)) ×
      Decidable (ExistsEntailsReg (h := 0) c φ (query x y)) ×
      Decidable (ExistsEntailsFin (h := 0) c φ (query x y))) ×'
    (Decidable (ExistsEntailsTopFree (h := 0) φ' (bfQuery x y)) ×
      Decidable (ExistsEntailsTopFreeReg (h := 0) φ' (bfQuery x y)) ×
      Decidable (ExistsEntailsTopFreeFin (h := 0) φ' (bfQuery x y))) ×'
    ((ExistsEntailsReg (h := 0) c φ (query x y) ↔ ExistsEntails (h := 0) c φ (query x y)) ∧
      (ExistsEntailsFin (h := 0) c φ (query x y) ↔
        (¬ ∃ ρ : V k → FTree n, ESat c (FTree.toTree ∘ ρ) φ) ∨
          ExistsEntails (h := 0) c φ (query x y))) :=
  ⟨⟨DeciENSSE.decideExistsEntails c φ (query x y),
      DeciENSSE.decideExistsEntailsReg c φ (query x y),
      DeciENSSE.decideExistsEntailsFin c φ (query x y)⟩,
    ⟨DeciENSSE.decideExistsEntailsTopFree φ' (bfQuery x y),
      DeciENSSE.decideExistsEntailsTopFreeReg φ' (bfQuery x y),
      DeciENSSE.decideExistsEntailsTopFreeFin φ' (bfQuery x y)⟩,
    existsEntailsReg_query_iff c φ x y, existsEntailsFin_query_iff c φ x y⟩

end DeciENSSE.Paper
