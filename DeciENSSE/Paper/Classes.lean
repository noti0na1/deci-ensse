import DeciENSSE.Main
import DeciENSSE.Bounds
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Support.RankedExtension

/-! # Paper contract: Tree Classes and the Signature without Top

Contract entries for the section *Tree Classes and the Signature without Top* (`sec:tc`) and
its appendix (`app:tc`): the extension criterion, two seeds, observation pins, closure under
intersection, regular and finite bound pinning, signed bounds and medians, the regular and
finite tree classes and their decision, and the reduction of `{⊥, f}` to `{⊥, f, ⊤}` by the
top-freeness gadget.

Only library results and logical packaging are used below. Finite variable
carriers represent the finite sets of variables in the paper. Systems and
finite collections of bounds are lists; regular and finite trees are images
of finite graphs and finite terms, respectively.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Core.Mixed
open Core.Mixed.FinitePinning Support.Median

variable {n : ℕ} {V X Z : Type*}

/-- **Lemma (Extension criterion)**, `lem:tc-extension`.
Form: Consistency separates forbidden roots from exclusion pairs; visible equality is inclusion because seeds are retained. The decoded extension is also least in the information order. Visible and hidden carriers may be infinite.
-/
theorem lem_tc_extension (c : Fin n → Bool) (ρ : X → Tree n)
    (ψ : List (LitT n (X ⊕ Z))) :
    ((∃ σ, SatT c (Sum.elim ρ σ) ψ) ↔
      Avoids ψ (Hull c ψ (visibleSeeds c ρ)) ∧
      Consistent (Hull c ψ (visibleSeeds c ρ)) ∧
      restrict (Hull c ψ (visibleSeeds c ρ)) ⊆ configSet c ρ) ∧
    ((∃ σ, SatT c (Sum.elim ρ σ) ψ) →
      ∃ σ, SatT c (Sum.elim ρ σ) ψ ∧
        configSet c (Sum.elim ρ σ) = Hull c ψ (visibleSeeds c ρ) ∧
        ∀ τ, SatT c (Sum.elim ρ τ) ψ →
          configSet c (Sum.elim ρ σ) ⊆ configSet c (Sum.elim ρ τ)) :=
  ⟨extends_iff_hull ρ ψ, least_extension ρ ψ⟩

/-- **Lemma (Two seeds)**, `lem:tc-two-seeds`.
Form: The asserted and denied sets are a list of at most two signed observations. The result also holds for infinite visible and hidden carriers.
-/
theorem lem_tc_two_seeds (c : Fin n → Bool) (ψ : List (LitT n (X ⊕ Z)))
    (ρ : X → Tree n) (hne : ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) :
    ∃ O : List (Core.Mixed.Observation n X), O.length ≤ 2 ∧
      (∀ o ∈ O, o.Holds c ρ) ∧
      ∀ ρ', (∀ o ∈ O, o.Holds c ρ') → ¬ ∃ σ, SatT c (Sum.elim ρ' σ) ψ :=
  two_observations_mixed ρ hne

/-- **Lemma (Observation pins)**, `lem:tc-pins`.
Form: The four covariant cases are packaged by Observation.bound; signed observations package the mixed cases. Bounds contain finite terms.
-/
theorem lem_tc_pins :
    (∀ (ρ : V → Tree n) (o : Core.Full.Observation n V),
      o.bound.Holds (fun _ => false) ρ ↔ o.Holds ρ) ∧
    (∀ (c : Fin n → Bool) (ρ : V → Tree n) (o : Core.Mixed.Observation n V),
      (o.bound c).Holds c ρ ↔ o.Holds c ρ) :=
  ⟨observation_bound, observation_bound_mixed⟩

/-- **Proposition (Closure under intersection)**, `prop:ch-meet`(1).
Form: Models and projected models are sets of signed atoms; their intersection closure packages the assignment-level consequence. Intersection closure also holds over arbitrary variable carriers.
-/
theorem prop_ch_meet_1 (c : Fin n → Bool) (χ : List (LitT n V))
    (ψ : List (LitT n (X ⊕ Z))) :
    (∀ (F : Set (Set (Config n V))), F.Nonempty →
      (∀ S ∈ F, Sol c χ S) → Sol c χ (⋂₀ F)) ∧
    (∀ (F : Set (Set (Config n X))), F.Nonempty →
      F ⊆ Projected c ψ → ⋂₀ F ∈ Projected c ψ) :=
  ⟨fun _ => sol_sInter, fun _ => projected_sInter ψ⟩

/-- **Proposition (Closure under intersection)**, `prop:ch-meet`(2).
Form: Positive arity is witnessed by a child index; infinitude is absence of a finite-term presentation.
-/
theorem prop_ch_meet_2 (c : Fin n → Bool) (i : Fin n) :
    infoInter c Tree.bot Tree.top = (RGraph.allF n).unfold ∧
    ¬ FiniteTop (RGraph.allF n).unfold :=
  ⟨infoInter_bot_top c, allF_not_finite i⟩

/-- **Lemma (Regular-bound pinning)**, `lem:tc-pinning-regular`.
Form: The variable set V is finite, as in the definition of a system; regular bounds are bindings to a finite indexed family of finite graphs.
-/
theorem lem_tc_pinning_regular {I : Type*} [Fintype V] [Fintype I]
    (c : Fin n → Bool) (χ : List (LitT n V)) (g : I → RGraph n)
    (B : List (TopGraphs.Binding V I))
    (hs : ∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, TopGraphs.bindingHolds c g ρ b) :
    ∃ τ, (∀ v, RegularTop (τ v)) ∧ SatT c τ χ ∧
      ∀ b ∈ B, TopGraphs.bindingHolds c g τ b :=
  TopGraphs.regularize c χ g B hs

/-- **Theorem (Finite-bound pinning)**, `thm:tc-pinning`.
Form: Bounds are a finite list of finite-term comparisons; finiteness means having a finite-term presentation.
-/
theorem thm_tc_pinning (c : Fin n → Bool) (χ : List (LitT n V))
    (hf : SatFin c χ) (B : List (GroundBound n V))
    (hs : ∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, b.Holds c ρ) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT c τ χ ∧ ∀ b ∈ B, b.Holds c τ :=
  finite_bound_realization c χ hf B hs

/-- **Lemma (Signed bounds)**, `lem:tc-signed`(1).
Form: System satisfaction and satisfaction of the bound list are paired as a conjunction.
-/
theorem lem_tc_signed_1 (c : Fin n → Bool) (χ : List (LitT n V))
    (B : List (GroundBound n V)) (ρ : V → Tree n) :
    (SatT c ρ χ ∧ ∀ b ∈ B, b.Holds c ρ) ↔
      (SatT (fun _ => false) (normalize c ρ) (Core.Full.signed c χ) ∧
        ∀ p ∈ pins c B, p.Holds (fun _ => false) (normalize c ρ)) :=
  and_congr (sat_normalize_iff c ρ χ).symm (pins_normalize_iff c B ρ).symm

/-- **Lemma (Signed bounds)**, `lem:tc-signed`(2).
-/
theorem lem_tc_signed_2 (c : Fin n → Bool) (χ : List (LitT n V))
    (B : List (GroundBound n V)) (A : V × Bool → Tree n) (ρ : V → Tree n) :
    signDual (signDual A) = A ∧
    ((SatT (fun _ => false) A (Core.Full.signed c χ) ∧
      ∀ p ∈ pins c B, p.Holds (fun _ => false) A) →
      SatT (fun _ => false) (signDual A) (Core.Full.signed c χ) ∧
        ∀ p ∈ pins c B, p.Holds (fun _ => false) (signDual A)) ∧
    signDual (normalize c ρ) = normalize c ρ :=
  ⟨signDual_involutive A, fun h => ⟨sat_signDual h.1, pins_signDual h.2⟩,
    normalize_fixed c ρ⟩

/-- **Lemma (Signed bounds)**, `lem:tc-signed`(3).
Form: Finiteness is existence of finite-term presentations; the inverse is the library function decode. Finiteness of decode does not require dual coherence.
-/
theorem lem_tc_signed_3 (c : Fin n → Bool) (A : V × Bool → Tree n) (ρ : V → Tree n) :
    (signDual A = A → normalize c (decode c A) = A) ∧
    ((∀ z, FiniteTop (normalize c ρ z)) ↔ ∀ v, FiniteTop (ρ v)) ∧
    ((∀ z, FiniteTop (A z)) → ∀ v, FiniteTop (decode c A v)) :=
  ⟨normalize_decode c, normalize_class_iff (finiteTop_normalize_iff c) ρ,
    decode_class (finiteTop_normalize_iff c)⟩

/-- **Lemma (Median)**, `lem:tc-median`(1).
Form: Monotonicity in the three arguments is packaged as simultaneous monotonicity.
-/
theorem lem_tc_median_1 (a b d : Tree n) :
    treeMedian a b d = treeMedian b a d ∧ treeMedian a a d = a ∧
    ∀ a' b' d', a ≤ a' → b ≤ b' → d ≤ d' →
      treeMedian a b d ≤ treeMedian a' b' d' :=
  ⟨treeMedian_swap a b d, treeMedian_self a d, fun _ _ _ => treeMedian_mono⟩

/-- **Lemma (Median)**, `lem:tc-median`(2).
-/
theorem lem_tc_median_2 (a b d : Fin n → Tree n) (t u v : Tree n)
    (A B D : V × Bool → Tree n) :
    treeMedian (DeciNSSE.Tree.node a) (DeciNSSE.Tree.node b) (DeciNSSE.Tree.node d) =
      DeciNSSE.Tree.node (fun i => treeMedian (a i) (b i) (d i)) ∧
    Tree.dual (treeMedian t u v) = treeMedian (Tree.dual t) (Tree.dual u) (Tree.dual v) ∧
    signDual (fun z => treeMedian (A z) (B z) (D z)) =
      fun z => treeMedian (signDual A z) (signDual B z) (signDual D z) :=
  ⟨treeMedian_node a b d, d_treeMedian t u v,
    funext fun z => d_treeMedian (A (z.1, !z.2)) (B (z.1, !z.2)) (D (z.1, !z.2))⟩

/-- **Lemma (Median)**, `lem:tc-median`(3).
Form: Finite trees are trees with a finite domain.
-/
theorem lem_tc_median_3 {a b d : Tree n}
    (ha : (Characterization.domain a).Finite) (hb : (Characterization.domain b).Finite)
    (hd : (Characterization.domain d).Finite) :
    (Characterization.domain (treeMedian a b d)).Finite :=
  finite_treeMedian ha hb hd

/-- **Lemma (Median)**, `lem:tc-median`(4).
Form: System closure and closure of arbitrary lower and upper ground bounds are packaged separately.
-/
theorem lem_tc_median_4 (χ : List (LitT n V)) (A B D : V → Tree n)
    (ha : SatT (fun _ => false) A χ) (hb : SatT (fun _ => false) B χ)
    (hd : SatT (fun _ => false) D χ) :
    SatT (fun _ => false) (fun v => treeMedian (A v) (B v) (D v)) χ ∧
    (∀ (v : V) (g : Tree n), g ≤ A v → g ≤ B v → g ≤ D v →
      g ≤ treeMedian (A v) (B v) (D v)) ∧
    (∀ (v : V) (g : Tree n), A v ≤ g → B v ≤ g → D v ≤ g →
      treeMedian (A v) (B v) (D v) ≤ g) := by
  refine ⟨sat_median ha hb hd, ?_, ?_⟩
  · intro v g h₁ h₂ h₃
    simpa only [treeMedian_self] using treeMedian_mono h₁ h₂ h₃
  · intro v g h₁ h₂ h₃
    simpa only [treeMedian_self] using treeMedian_mono h₁ h₂ h₃

/-- **Lemma (Covariant finite-bound pinning)**, `lem:tc-pinning-covariant`.
Form: Bounds are a finite list of finite-term comparisons.
-/
theorem lem_tc_pinning_covariant (χ : List (LitT n V))
    (hf : SatFin (fun _ => false) χ) (B : List (GroundBound n V))
    (hs : ∃ ρ, SatT (fun _ => false) ρ χ ∧ ∀ b ∈ B, b.Holds (fun _ => false) ρ) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ χ ∧
      ∀ b ∈ B, b.Holds (fun _ => false) τ :=
  finite_bound_realization (fun _ => false) χ hf B hs

/-- **Theorem (Regular trees)**, `thm:tc-regular`(1).
Form: The variable set V is finite, as in the definition of a system; regularity is existence of a finite-graph presentation.
-/
theorem thm_tc_regular_1 [Fintype V] (c : Fin n → Bool) (χ : List (LitT n V)) :
    (∃ ρ, SatT c ρ χ) ↔ SatisfiableIn RegularTop c χ :=
  ⟨satisfiable_regular c, fun ⟨ρ, _, h⟩ => ⟨ρ, h⟩⟩

/-- **Theorem (Regular trees)**, `thm:tc-regular`(2).
Form: ClassExtension quantifies the regular visible assignment and its extension.
-/
theorem thm_tc_regular_2 [Fintype X] [Fintype Z]
    (c : Fin n → Bool) (ψ : List (LitT n (X ⊕ Z))) : ClassExtension RegularTop c ψ :=
  regular_class_extension c ψ

/-- **Theorem (Regular trees)**, `thm:tc-regular`(3).
Form: This item also packages the theorem's unnumbered entailment equivalence; regularity uses finite-graph presentations.
-/
theorem thm_tc_regular_3 [Fintype X] [Fintype Z]
    (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    ((∃ ρ, SatT c ρ φ ∧ ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) →
      ∃ ρ, (∀ x, RegularTop (ρ x)) ∧ SatT c ρ φ ∧
        ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) ∧
    (ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ) := by
  refine ⟨?_, existsEntailsTReg_iff_mixed c φ ψ⟩
  rintro ⟨ρ, hρ, hn⟩
  obtain ⟨O, hO, ho, hne⟩ := two_observations_mixed ρ hn
  obtain ⟨τ, hc, ht, hp⟩ := (regular_bound_realization c φ).observations ρ hρ O hO ho
  exact ⟨τ, hc, ht, hne τ hp⟩

/-- **Theorem (Finite trees)**, `thm:tc-finite`(1).
Form: Finiteness is existence of a finite-term presentation. Visible and hidden carriers may be infinite.
-/
theorem thm_tc_finite_1 (c : Fin n → Bool) (φ : List (LitT n X))
    (ψ : List (LitT n (X ⊕ Z))) (hf : SatFin c φ)
    (hn : ∃ ρ, SatT c ρ φ ∧ ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ) :
    ∃ ρ, (∀ x, FiniteTop (ρ x)) ∧ SatT c ρ φ ∧ ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  obtain ⟨ρ, hρ, hn⟩ := hn
  obtain ⟨O, hO, ho, hne⟩ := two_observations_mixed ρ hn
  obtain ⟨τ, hc, ht, hp⟩ := (finite_bound_realization c φ hf).observations ρ hρ O hO ho
  exact ⟨τ, hc, ht, hne τ hp⟩

/-- **Theorem (Finite trees)**, `thm:tc-finite`(2).
Form: ClassExtension packages extension of finite assignments; this item also includes the theorem's unnumbered finite dispatch equivalence. Only the visible carrier is required to be finite.
-/
theorem thm_tc_finite_2 [Fintype X] (c : Fin n → Bool)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    (SatFin c ψ → ClassExtension FiniteTop c ψ) ∧
    (ExistsEntailsTFin c φ ψ ↔ ¬ SatFin c φ ∨ (SatFin c ψ ∧ ExistsEntailsT c φ ψ)) :=
  ⟨finite_class_extension, existsEntailsTFin_iff_mixed c φ ψ⟩

/-- **Corollary (Decisions for regular and finite trees)**, `cor:tc-decidable`.
Form: The conditional is a computable transformer at fixed finite carriers. A decision procedure over arbitrary trees yields one over regular trees through the regular equivalence, and one over finite trees through the finite dispatch, whose two finite-satisfiability tests run Core.Mixed.decideSatFin. Both equivalences are included.
-/
def cor_tc_decidable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (c : Fin n → Bool) :
    ((∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))), Decidable (ExistsEntailsT c φ ψ)) →
      (∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))),
        Decidable (ExistsEntailsTReg c φ ψ)) ×'
      (∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))),
        Decidable (ExistsEntailsTFin c φ ψ))) ×'
    (∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))),
      (ExistsEntailsTReg c φ ψ ↔ ExistsEntailsT c φ ψ) ∧
      (ExistsEntailsTFin c φ ψ ↔ ¬ SatFin c φ ∨ (SatFin c ψ ∧ ExistsEntailsT c φ ψ))) :=
  ⟨fun d =>
    ⟨fun φ ψ => @decidable_of_iff _ _ (existsEntailsTReg_iff_mixed c φ ψ).symm (d φ ψ),
      fun φ ψ =>
        letI := Core.Mixed.decideSatFin c φ
        letI := Core.Mixed.decideSatFin c ψ
        letI := d φ ψ
        decidable_of_iff _ (existsEntailsTFin_iff_mixed c φ ψ).symm⟩,
    fun φ ψ => ⟨existsEntailsTReg_iff_mixed c φ ψ, existsEntailsTFin_iff_mixed c φ ψ⟩⟩

/-- **Lemma (Top-freeness gadget)**, `lem:tc-gadget`(1).
-/
theorem lem_tc_gadget_1 {y : Tree n} (hy : y ≤ DeciNSSE.Tree.node fun _ => y) :
    TopFree y ∧ ∀ t : Tree n, t ≤ y → TopFree t :=
  ⟨TopFree.of_le_node hy, fun _ ht => TopFree.mono (TopFree.of_le_node hy) ht⟩

/-- **Lemma (Top-freeness gadget)**, `lem:tc-gadget`(2).
Form: Omega is the unfolding of the one-state graph. Finite trees use finite terms; height counts constructors (at arity zero the witness is still f()).
-/
theorem lem_tc_gadget_2 :
    (∀ t : Tree n, TopFree t → TopFree.IsWitness t (RGraph.allF n).unfold) ∧
    RegularTop (RGraph.allF n).unfold ∧
    (∀ a : FTree n, TopFree a.toTree →
      TopFree.IsWitness a.toTree (FTree.full (a.height + 1)).toTree) :=
  ⟨fun _ => TopFree.isWitness_allF, ⟨RGraph.allF n, rfl⟩, fun _ => FTree.isWitness_full⟩

/-- **Theorem (Reduction of bottom-constructor to full signature)**, `thm:tc-gadget`.
Form: The three tree classes are a conjunction. Fresh variables are sum copies; lists enumerate all visible and hidden variables. Top-free values interpret the smaller signature. The equivalences also allow full-syntax systems interpreted with top-free values; the paper uses their specialization without top literals.
-/
theorem thm_tc_gadget {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z} (hzs : ∀ z, z ∈ zs)
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    (ExistsEntailsTIn TopFree (fun _ => false) φ ψ ↔
      ExistsEntailsT (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ)) ∧
    (ExistsEntailsTIn (fun t => TopFree t ∧ RegularTop t) (fun _ => false) φ ψ ↔
      ExistsEntailsTReg (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ)) ∧
    (ExistsEntailsTIn (fun t => TopFree t ∧ FiniteTop t) (fun _ => false) φ ψ ↔
      ExistsEntailsTFin (fun _ => false) (TopFree.gadgetAnte xs φ) (TopFree.gadgetCons zs ψ)) :=
  ⟨TopFree.existsEntailsT_iff_gadget hxs hzs φ ψ,
    TopFree.existsEntailsTReg_iff_gadget hxs hzs φ ψ,
    TopFree.existsEntailsTFin_iff_gadget hxs hzs φ ψ⟩

/-- **Corollary (The bottom-constructor signature)**, `cor:tc-bf`.
Form: Fin-indexed public syntax, with k visible and h hidden variables. Each conditional is a computable transformer: a decision procedure for the covariant problem over the full signature, on the doubled carriers, yields one for the bottom-constructor signature in the same tree class, through the reduction toCoreTopFree and splitTopFree. The three reductions and the regular/arbitrary equivalence are included. The size claims are the doubled carriers Sum (Fin k) (Fin k) and Sum (Fin h) (Fin h) and the translated lengths, two more literals per visible or hidden variable.
-/
def cor_tc_bf {k h : ℕ} :
    ((∀ (φ : List (LitT n (Fin k ⊕ Fin k)))
        (ψ : List (LitT n ((Fin k ⊕ Fin k) ⊕ (Fin h ⊕ Fin h)))),
        Decidable (ExistsEntailsT (fun _ => false) φ ψ)) →
      ∀ (φ : BFConstraint n k) (ψ : BFConstraint n (k + h)),
        Decidable (ExistsEntailsTopFree φ ψ)) ×'
    ((∀ (φ : List (LitT n (Fin k ⊕ Fin k)))
        (ψ : List (LitT n ((Fin k ⊕ Fin k) ⊕ (Fin h ⊕ Fin h)))),
        Decidable (ExistsEntailsTReg (fun _ => false) φ ψ)) →
      ∀ (φ : BFConstraint n k) (ψ : BFConstraint n (k + h)),
        Decidable (ExistsEntailsTopFreeReg φ ψ)) ×'
    ((∀ (φ : List (LitT n (Fin k ⊕ Fin k)))
        (ψ : List (LitT n ((Fin k ⊕ Fin k) ⊕ (Fin h ⊕ Fin h)))),
        Decidable (ExistsEntailsTFin (fun _ => false) φ ψ)) →
      ∀ (φ : BFConstraint n k) (ψ : BFConstraint n (k + h)),
        Decidable (ExistsEntailsTopFreeFin φ ψ)) ×'
    (∀ (φ : BFConstraint n k) (ψ : BFConstraint n (k + h)),
      (ExistsEntailsTopFree φ ψ ↔
        ExistsEntailsT (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)) ∧
      (ExistsEntailsTopFreeReg φ ψ ↔
        ExistsEntailsTReg (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)) ∧
      (ExistsEntailsTopFreeFin φ ψ ↔
        ExistsEntailsTFin (fun _ => false) (toCoreTopFree φ) (splitTopFree ψ)) ∧
      (ExistsEntailsTopFreeReg φ ψ ↔ ExistsEntailsTopFree φ ψ) ∧
      (toCoreTopFree φ).length = φ.length + 2 * k ∧
      (splitTopFree ψ).length = ψ.length + 2 * h) ∧
    (Fintype.card (Fin k ⊕ Fin k) = 2 * k ∧ Fintype.card (Fin h ⊕ Fin h) = 2 * h ∧
      Fintype.card (Fin k ⊕ Fin k) + Fintype.card (Fin h ⊕ Fin h) = 2 * (k + h)) :=
  ⟨fun d φ ψ =>
      @decidable_of_iff _ _ (existsEntailsTopFree_iff_core φ ψ).symm
        (d (toCoreTopFree φ) (splitTopFree ψ)),
    fun d φ ψ =>
      @decidable_of_iff _ _ (existsEntailsTopFreeReg_iff_core φ ψ).symm
        (d (toCoreTopFree φ) (splitTopFree ψ)),
    fun d φ ψ =>
      @decidable_of_iff _ _ (existsEntailsTopFreeFin_iff_core φ ψ).symm
        (d (toCoreTopFree φ) (splitTopFree ψ)),
    fun φ ψ => ⟨existsEntailsTopFree_iff_core φ ψ, existsEntailsTopFreeReg_iff_core φ ψ,
      existsEntailsTopFreeFin_iff_core φ ψ, existsEntailsTopFreeReg_iff φ ψ,
      by simp [toCoreTopFree], by simp [splitTopFree, splitFull]⟩,
    by simpa using (Bounds.card_gadget_vars (X := Fin k) (Z := Fin h)).1,
    by simpa using (Bounds.card_gadget_vars (X := Fin h) (Z := Fin k)).1,
    by simpa using (Bounds.card_gadget_vars (X := Fin k) (Z := Fin h)).2⟩

/-- **Lemma (Ground bounds as path pins)**, `lem:tc-ground-pins`.
Form: The recursive list groundPins enumerates constructor and extreme-leaf positions; a Boolean selects lower or upper bounds, and PathPin.Holds interprets their observations. The equivalence also holds at arity zero.
-/
theorem lem_tc_ground_pins (v : V) (lower : Bool) (g : FTree n) (ρ : V → Tree n) :
    (∀ p ∈ Pinning.groundPins v lower g, p.Holds ρ) ↔
      (if lower then g.toTree ≤ ρ v else ρ v ≤ g.toTree) :=
  Pinning.groundPins_iff v lower g ρ

/-- **Lemma (Ranked extensions)**, `lem:tc-ranked`.
Form: Finite variable sets are initial segments; Ranked.Extension packages the embedding, source/sink partition, and rank assumptions. Old ranks need not be zero; the result also holds at arity zero.
-/
theorem lem_tc_ranked {k m : ℕ} {φ : Constraint n k} {ψ : Constraint n (k + m)}
    {Source Sink : DeciNSSE.V (k + m) → Prop} {rank : DeciNSSE.V (k + m) → ℕ}
    (e : Ranked.Extension (Fin.castAdd m) φ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash φ :=
  Support.RankedExtension.extension_cycleClash_iff e

end DeciENSSE.Paper
