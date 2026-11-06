import DeciENSSE.Main
import DeciENSSE.TopFree
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Support.Normalization
import DeciNSSE.RejectedTail.Decision
import DeciENSSE.Support.HoleCorrespondence

/-! # Paper contract: Background

Contract entries for the section *Background* (`sec:bg`), except the flattening lemma of
`DeciENSSE.Paper.Flattening`, and for the appendix *Results Used from the Plain-Entailment
Proof* (`app:bg`): periodic prefixes, normalization, the order over `{⊥, f}`, the signed
correspondence, sandwich elimination, regular and finite solutions, satisfiability, and the
facts about readers, rejected tails, the canonical hierarchy and the bounded-depth hole
search that the proof takes from the plain-entailment library `DeciNSSE`.
-/
namespace DeciENSSE.Paper
open DeciNSSE Core.Full Core.Mixed
open Core.Mixed.FinitePinning Core.Full.Flatten
open scoped List
variable {n k : ℕ} {V : Type*}

/-- **Lemma (Periodic prefixes)**, `lem:bg-periodic`.
Form: The infinite repetition is a periodic stream; its arbitrary default letter is immaterial for a nonempty period.
-/
theorem lem_bg_periodic {α : Type*} [Inhabited α] (o θ : List α) (ho : o ≠ []) :
    θ <+: o ++ θ ↔ Core.Words.IsStreamPrefix θ (Core.Words.periodicStream o) :=
  Core.Words.periodic_prefix_iff ho

/-- **Lemma (Normalization)**, `lem:bg-normalization`(1). -/
theorem lem_bg_normalization_1 (c : Fin n → Bool) (s : Bool) (t : Tree n)
    (a : Fin n → Tree n) :
    Tree.normalize c s (DeciNSSE.Tree.node a) =
      DeciNSSE.Tree.node (fun i => Tree.normalize c (Bool.xor s (c i)) (a i)) ∧
    Tree.normalize c true t = Tree.dual (Tree.normalize c false t) ∧
    Tree.normalize c true t = Tree.normalize c false (Tree.dual t) ∧
    Tree.normalize c s (Tree.normalize c s t) = t :=
  ⟨normalize_node c s a, normalize_true c t, (Support.normalize_dual c false t).symm,
    normalize_involutive c s t⟩

/-- **Lemma (Normalization)**, `lem:bg-normalization`(2).
Form: The chained equivalence is two equivalences with the same left-hand side.
-/
theorem lem_bg_normalization_2 (c : Fin n → Bool) (t u : Tree n) :
    (Tree.Le c t u ↔ Tree.normalize c false t ≤ Tree.normalize c false u) ∧
    (Tree.Le c t u ↔ Tree.normalize c true u ≤ Tree.normalize c true t) :=
  ⟨treeLe_iff_normalize c t u, Support.treeLe_iff_normalize_true c t u⟩

/-- **Lemma (Normalization)**, `lem:bg-normalization`(3). -/
theorem lem_bg_normalization_3 (t u : Tree n) : t ≤ u ↔ Tree.dual u ≤ Tree.dual t :=
  (dual_le_iff u t).symm

/-- **Lemma (Normalization)**, `lem:bg-normalization`(4).
Form: Subtrees are optional, so the identity also covers words outside the domain; regularity means finitely many subtrees.
-/
theorem lem_bg_normalization_4 (c : Fin n → Bool) (s : Bool) (t : Tree n) (w : List (Fin n)) :
    (Tree.normalize c s t).subtree w =
      (t.subtree w).map (Tree.normalize c (Bool.xor s (polarity c w))) ∧
    Characterization.domain (Tree.normalize c s t) = Characterization.domain t ∧
    ((Characterization.domain (Tree.normalize c s t)).Finite ↔ (Characterization.domain t).Finite) ∧
    ((Characterization.subtrees (Tree.normalize c s t)).Finite ↔ (Characterization.subtrees t).Finite) ∧
    Characterization.domain (Tree.dual t) = Characterization.domain t ∧
    ((Characterization.domain (Tree.dual t)).Finite ↔ (Characterization.domain t).Finite) ∧
    ((Characterization.subtrees (Tree.dual t)).Finite ↔ (Characterization.subtrees t).Finite) :=
  ⟨Support.subtree_normalize c s t w, Support.domain_normalize c s t,
    Support.finite_domain_normalize_iff c s t, Support.finite_subtrees_normalize_iff c s t,
    Support.domain_normalize (fun _ => false) true t,
    Support.finite_domain_normalize_iff (fun _ => false) true t,
    Support.finite_subtrees_normalize_iff (fun _ => false) true t⟩

/-- **Lemma (Order over bottom and constructor)**, `lem:bg-bf-order`.
Form: TopFree expresses the smaller signature; constructor positions are tested by their labels.
-/
theorem lem_bg_bf_order (t u : Tree n) (ht : TopFree t) (hu : TopFree u) :
    t ≤ u ↔ ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f :=
  TopFree.le_iff_constructor_subset ht hu

/-- **Lemma (Signed correspondence)**, `lem:bg-signed`.
Form: Dual coherence is the equation signDual A = A; finite and regular trees use finite-term and finite-graph presentations. Existence and uniqueness express the bijection. The class-preservation claims for decode hold without dual coherence.
-/
theorem lem_bg_signed (c : Fin n → Bool) (χ : List (LitT n V)) :
    (∀ ρ, SatT c ρ χ ↔ SatT (fun _ => false) (normalize c ρ) (Core.Full.signed c χ)) ∧
    (∀ ρ : V → Tree n, signDual (normalize c ρ) = normalize c ρ) ∧
    (∀ A : V × Bool → Tree n, signDual A = A → ∃! ρ, normalize c ρ = A) ∧
    (∀ ρ : V → Tree n, ((∀ z, FiniteTop (normalize c ρ z)) ↔ ∀ v, FiniteTop (ρ v)) ∧
      ((∀ z, RegularTop (normalize c ρ z)) ↔ ∀ v, RegularTop (ρ v))) ∧
    (∀ A : V × Bool → Tree n,
      ((∀ z, FiniteTop (A z)) → ∀ v, FiniteTop (FinitePinning.decode c A v)) ∧
      ((∀ z, RegularTop (A z)) → ∀ v, RegularTop (FinitePinning.decode c A v))) := by
  refine ⟨fun ρ => (sat_normalize_iff c ρ χ).symm, normalize_fixed c, ?_,
    fun ρ => ⟨normalize_class_iff (finiteTop_normalize_iff c) ρ,
      normalize_class_iff (regularTop_normalize_iff c) ρ⟩,
    fun _ => ⟨decode_class (finiteTop_normalize_iff c), decode_class (regularTop_normalize_iff c)⟩⟩
  intro A hA
  refine ⟨FinitePinning.decode c A, normalize_decode c hA, ?_⟩
  intro ρ hρ
  funext v
  have h := congrArg (fun B => Tree.normalize c false (B (v, false))) hρ
  simpa only [normalize, normalize_involutive, FinitePinning.decode] using h

/-- **Lemma (Sandwich elimination)**, `lem:bg-sandwich`.
Form: Positive arity is a NeZero instance; sandwichArgs selects argument zero and repeats the filler elsewhere.
-/
theorem lem_bg_sandwich [NeZero n] (c : Fin n → Bool) (u v : Tree n) :
    Tree.Le c u v ↔ ∃ y : Tree n,
      Tree.Le c (DeciNSSE.Tree.node (sandwichArgs (if c 0 then v else u) u)) y ∧
      Tree.Le c y (DeciNSSE.Tree.node (sandwichArgs (if c 0 then u else v) u)) := by
  constructor
  · intro h
    exact ⟨_, treeLe_refl c _, (sandwich_iff c u v).mpr h⟩
  · rintro ⟨y, h₁, h₂⟩
    exact (sandwich_iff c u v).mp (treeLe_trans h₁ h₂)

/-- **Theorem (Regular and finite solutions)**, `thm:bg-nsse`(1).
Form: The variable set V is finite, as in the definition of a system; finite-graph presentations express regular satisfiability.
-/
theorem thm_bg_nsse_1 [Fintype V] (c : Fin n → Bool) (χ : List (LitT n V)) :
    SatisfiableIn RegularTop c χ ↔ ∃ ρ, SatT c ρ χ :=
  ⟨fun ⟨ρ, _, h⟩ => ⟨ρ, h⟩, satisfiable_regular c⟩

/-- **Theorem (Regular and finite solutions)**, `thm:bg-nsse`(2).
Form: Decidability is a computable definition, the executable finite-satisfiability procedure Core.Mixed.decideSatFin on systems over a finite variable carrier.
-/
def thm_bg_nsse_2 [Fintype V] [DecidableEq V] (c : Fin n → Bool) (χ : List (LitT n V)) :
    Decidable (SatFin c χ) := Core.Mixed.decideSatFin c χ

/-- **Theorem (Satisfiability criteria)**, `thm:bg-nsse-sat`(1).
Form: Variables are Fin k; finite solutions are finite terms. The cycle witness bound is k * k.
-/
theorem thm_bg_nsse_sat_1 (χ : Constraint n k) :
    (∀ ρ, Covariant.Sat ρ χ → ∀ u v, Derives χ u v → ρ u ≤ ρ v) ∧
    ((∃ ρ, Covariant.Sat ρ χ) ↔ ¬ LabelClash χ) ∧
    ((∃ σ : DeciNSSE.V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ) ↔
      ¬ LabelClash χ ∧ ¬ CycleClash χ) ∧
    (¬ LabelClash χ → (CycleClash χ ↔ ∃ η a b,
      0 < η.length ∧ η.length ≤ k * k ∧ LowerAt χ η a a ∧ Derives χ a b ∧ UpperAt χ η b b)) :=
  ⟨fun _ h _ _ hd => hd.sound _ h, satisfiable_iff_not_labelClash,
    satFin_iff, cycleClash_iff_bounded⟩

/-- **Theorem (Satisfiability criteria)**, `thm:bg-nsse-sat`(2).
Form: Variables are Fin k, with signed variables Fin (2 * k); finite solutions are finite terms.
-/
theorem thm_bg_nsse_sat_2 (c : Fin n → Bool) (χ : Constraint n k) :
    (Satisfiable c χ ↔ ∃ A, Covariant.Sat A (DeciNSSE.signed c χ)) ∧
    (SatisfiableFin c χ ↔ ∃ σ : DeciNSSE.V (2 * k) → FTree n,
      Covariant.Sat (FTree.toTree ∘ σ) (DeciNSSE.signed c χ)) :=
  ⟨sat_iff_signed_sat c χ, satFin_iff_signed c χ⟩

/-- **Theorem (Satisfiability criteria)**, `thm:bg-nsse-sat`(3).
Form: Variables are Fin k and regular solutions are finite-graph assignments.
-/
theorem thm_bg_nsse_sat_3 (c : Fin n → Bool) (χ : Constraint n k) :
    Satisfiable c χ → ∃ σ : DeciNSSE.V k → RGraph n, Sat c (RGraph.unfold ∘ σ) χ :=
  (Support.Graphs.satReg_iff_sat c χ).mpr

open DeciNSSE.Holes DeciNSSE.RejectedTail DeciNSSE.CoAlignment
open DeciNSSE.LetteredHierarchy DeciNSSE.HierarchyDepth DeciNSSE.BoundedDepth
open DeciNSSE.NormalForm DeciNSSE.ElementaryBound DeciNSSE.Exchange
open DeciNSSE.LevelMaps DeciNSSE.BoundaryPairs DeciNSSE.CoreOccurrences DeciNSSE.Cores

/-- **Lemma (Rejected extension)**, `lem:bg-extension`.
Form: The result holds without finiteness assumptions on the alphabet or the state carrier.
-/
theorem lem_bg_extension {α Q : Type*} (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [RejectedPath M R T] {v w : List α} (hv : IsReaderHole M R T v)
    (hvw : v <+: w) (hw : M.eval w ∈ T) : IsReaderHole M R T w :=
  rejected_extension M R T hv hvw hw

/-- **Theorem (Bounded rejected tail)**, `thm:bg-brt`.
Form: BoundedRejectedTail existentially selects a hole and its first rejected cut, with tail length at most the displayed bound. The alphabet need not be finite.
-/
theorem thm_bg_brt {α Q : Type*} [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [RejectedPath M R T] :
    BoundedRejectedTail M R T (4 * Fintype.card Q - 2) :=
  boundedRejectedTail_of_rejectedPath M R T

/-- **Lemma (Alignment)**, `lem:bg-alignment`.
Form: Strict cut inequalities are hypotheses; the two comparison predicates are expressed by their suffix-prefix conditions.
-/
theorem lem_bg_alignment {Γ : Type*} [DecidableEq Γ] (ℓ : Γ) (v : List (List Γ))
    (hv : ∀ X ∈ v, ℓ ∉ X) {s e : ℕ} (hse : s < e) (he : e < (expand ℓ v).length) :
    (expand ℓ v).drop e <+: (expand ℓ v).drop s ↔
      ∃ ks ke, ∃ (hks : ks < v.length) (hke : ke < v.length), ks < ke ∧
        ∃ xs xe y, v[ks] = xs ++ y ∧ v[ke] = xe ++ y ∧
          s = cutP ℓ v ks + xs.length ∧ e = cutP ℓ v ke + xe.length ∧
          v.drop (ke + 1) <+: v.drop (ks + 1) :=
  LetteredHierarchy.alignment ℓ v hv hse he

/-- **Lemma (Return gap)**, `lem:bg-return-gap`.
Form: ReturnGap quantifies the rejected word, its first rejected cut, and the comparison with equal states. The return-gap statement needs neither finite states nor a finite alphabet.
-/
theorem lem_bg_return_gap {α Q : Type*} (M : DFA α Q) (T : Set Q) : ReturnGap M T :=
  return_gap M T

/-- **Theorem (Depth from the rejected tail)**, `thm:bg-depth`.
Form: J is the first rejected cut, so the tail length is w.length - J; a default letter defines the total canonical hierarchy. The alphabet need not be finite.
-/
theorem thm_bg_depth {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]
    (M : DFA α Q) (_R : Q → Q → Prop) (T : Set Q) {w : List α} {J : ℕ}
    (hw : w ≠ []) (hr : M.eval w ∈ T) (hJ : IsFirstRejectedPrefix M T w J) :
    depth w ≤ 2 * Fintype.card Q * (w.length - J + 1) - 1 :=
  rejected_depth M T hw hr hJ

/-- **Theorem (Bounded-depth search)**, `thm:bg-search`.
Form: InL d expresses depth at most d; lettered holes are nonempty by definition. Both monitor and reader forms are included; a default letter defines the total hierarchy. The reader version, like the monitor version, does not require a finite alphabet.
-/
theorem thm_bg_search {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q] (d : ℕ) :
    (∀ (D : Lettered α Q) (w : List α), D.IsHole w → InL d w →
      ∃ v, D.IsHole v ∧ InL d v ∧ v.length ≤ lengthBound (Fintype.card Q) d) ∧
    (∀ (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α),
      w ≠ [] → IsReaderHole M R T w → InL d w →
      ∃ v, v ≠ [] ∧ IsReaderHole M R T v ∧ InL d v ∧
        v.length ≤ lengthBound (Fintype.card Q) d) := by
  refine ⟨fun _ _ => exists_short_hole, ?_⟩
  intro M R T w hw hh hd
  obtain ⟨v, hv, hL, hlen⟩ := exists_short_hole
    ((isHole_ofReader_iff M R T hw).mpr hh) hd
  exact ⟨v, hv.ne_nil, (isHole_ofReader_iff M R T hv.ne_nil).mp hv, hL, hlen⟩

/-- **Corollary (Finite search for holes)**, `cor:bg-hole-decision`.
Form: holeLengthBound N is lengthBound N (2 * N * (4 * N - 1) - 1).
-/
theorem cor_bg_hole_decision {α Q : Type*} [DecidableEq α] [Fintype α]
    [Fintype Q] [DecidableEq Q] (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [RejectedPath M R T] :
    ((∃ w, IsReaderHole M R T w) ↔ ∃ w, IsReaderHole M R T w ∧
      w.length ≤ holeLengthBound (Fintype.card Q)) ∧
    holeLengthBound (Fintype.card Q) ≤ 2 ^ 2 ^ (1280 * (Fintype.card Q + 1) ^ 5) :=
  ⟨hole_iff_bounded_length M R T, holeLengthBound_le _⟩

/-- **Lemma (Holes under desubstitution)**, `lem:bg-desub`.
Form: The one-step equivalence is oriented from derivative to expansion; the canonical hierarchy uses a default letter. Cores Q j is the iterated option state type.
-/
theorem lem_bg_desub {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    (D : Lettered α Q) :
    (∀ (ℓ : α) (v : List (List α)), v ≠ [] → (∀ X ∈ v, ℓ ∉ X) →
      ((der D ℓ).IsHole v ↔ D.IsHole (expand ℓ v))) ∧
    (∀ (w : List α), w ≠ [] → ∀ j,
      ((tower D (markOf w) j).IsHole (hierOf w j) ↔ D.IsHole w)) ∧
    (∀ j, Fintype.card (LetteredHierarchy.Cores Q j) = Fintype.card Q + j) :=
  ⟨fun ℓ v hv ha => isHole_der_iff D ℓ v hv ha,
    fun _ hw j => isHole_hierOf_iff hw D j, card_cores⟩

/-- **Lemma (Cores)**, `lem:bg-cores`(1).
Form: Ordinary cores are original-word positions; symbolic cores are the iterated-option start states of a monitor. A default letter defines the total hierarchy.
-/
theorem lem_bg_cores_1 {α Q : Type*} [DecidableEq α] [Inhabited α]
    (D : Lettered α Q) (w : List α) (hw : w ≠ []) (j : ℕ) :
    ordinaryCores w (j + 1) ⊆ ordinaryCores w j ∧
    (∀ x < (hierOf w j).length,
      isStart j ((tower D (markOf w) j).core (hierOf w j) x) = true ↔ x < sCount D w j) ∧
    (∀ x y, x < (hierOf w j).length → y < (hierOf w j).length →
      isStart j ((tower D (markOf w) j).core (hierOf w j) x) = true →
      isStart j ((tower D (markOf w) j).core (hierOf w j) y) = true → x ≠ y →
      (tower D (markOf w) j).core (hierOf w j) x ≠ (tower D (markOf w) j).core (hierOf w j) y) ∧
    sCount D w j ≤ j ∧
    (∀ x y, x < y → y < (hierOf w j).length → ∀ p q,
      corePos w j x = some p → corePos w j y = some q → p < q) :=
  ⟨cores_succ_subset hw j, (startCore_invariants D hw j).1,
    (startCore_invariants D hw j).2.2.1, StartCores.sCount_le_level D hw j,
    Support.HoleCorrespondence.corePos_strict hw j⟩

/-- **Lemma (Cores)**, `lem:bg-cores`(2).
Form: IsGreatest supplies the maximum ordinary core; the set identity includes the asserted comparisons. A default letter defines the total hierarchy.
-/
theorem lem_bg_cores_2 {α : Type*} [DecidableEq α] [Inhabited α]
    (w : List α) (hw : w ≠ []) (j : ℕ) :
    ((ordinaryCores w j).Nonempty → ∃ e, IsGreatest (ordinaryCores w j) e ∧
      ordinaryCores w (j + 1) = {p | p < e ∧ w.drop e <+: w.drop p}) ∧
    (ordinaryCores w j = ∅ → ordinaryCores w (j + 1) = ∅) := by
  refine ⟨fun hn => ?_, fun he => ?_⟩
  · obtain ⟨e, he⟩ := cores_greatest hw j hn
    exact ⟨e, he, Support.HoleCorrespondence.ordinaryCores_succ hw he⟩
  · have h := cores_succ_subset hw j
    rw [he] at h
    exact Set.Subset.antisymm h (Set.empty_subset _)


/-- **Lemma (Exchange types)**, `lem:bg-exchange-types`.
Form: ClosedType is the finite type of exchange tables; normalTypeBound is C(N,d). A default letter defines the total hierarchy. The bound applies to the entire exchange-table type for any nonempty word satisfying the depth inequalities; holehood is not needed.
-/
theorem lem_bg_exchange_types {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] (D : Lettered α Q) (w : List α) (hw : w ≠ [])
    (i d : ℕ) (_hi : 1 ≤ i) (hid : i < depth w) (hd : depth w ≤ d) :
    Fintype.card (ClosedType (Qset Q i) (Uset D w i) (Pset D w i)) ≤
      normalTypeBound (Fintype.card Q) d :=
  Support.HoleCorrespondence.exchange_types_le D hw (Nat.le_trans hid.le hd)

/-- **Lemma (Comparison-preserving maps)**, `lem:bg-comparison-map`.
Form: NoCollapse states the predecessor-pair condition with zero-based letter indices.
-/
theorem lem_bg_comparison_map {α β : Type*} (v : List α) (ℓ : α) (hℓ : v.getLast? = some ℓ)
    (h : α → β) (hc : NoCollapse h v) :
    (∀ s e, IsComp (v.map h) s e ↔ IsComp v s e) ∧
    (∀ a ∈ v, h a = h ℓ → a = ℓ) :=
  ⟨hc.isComp_iff, hc.reflect_last hℓ⟩

/-- **Lemma (Shape under a level map)**, `lem:bg-level-maps`.
Form: LevelMapResult packages the hole, marker, dictionary, higher-map, start-count and unary-level claims; depth and dictionary cardinalities are also explicit. A default letter defines the total hierarchy. This structural result does not require finitely many monitor states.
-/
theorem lem_bg_level_maps {α Q : Type*} [DecidableEq α] [Inhabited α]
    (D : Lettered α Q) {w : List α} (hw : D.IsHole w) (i : ℕ)
    (f : Alph α i → Alph α i) (hc : NoCollapse f (hierOf w i))
    (hh : (tower D (markOf w) i).IsHole ((hierOf w i).map f))
    (hsub : ∀ a ∈ hierOf w i, f a ∈ hierOf w i)
    (hpre : ∀ a ∈ (hierOf w i).take (sCount D w i), f a = a)
    (hr : ∀ k, (tower D (markOf w) i).core ((hierOf w i).map f) k =
      (tower D (markOf w) i).core (hierOf w i) k) :
    let w' := expandTo (markOf w) i ((hierOf w i).map f)
    LevelMapResult D w i f w' ∧ depth w' = depth w ∧ ∀ j, alphCard w' j ≤ alphCard w j := by
  have h := levelMap_spec D hw i f hc hh hsub hpre hr
  exact ⟨h, h.depth_eq, alphCard_le_of_levelMap h⟩

/-- **Lemma (Isolated exchange)**, `lem:bg-isolated-exchange`.
Form: The first conjunct lists the hypotheses of lem:bg-level-maps for the map identify x y: no collapse of predecessor pairs, the mapped-level hole, dictionary containment, the fixed start prefix and the unchanged run of cores. LevelMapResult includes the unchanged start counts and unary levels; letterWeight is the level-zero expansion length. A default letter defines the total hierarchy.
-/
theorem lem_bg_isolated_exchange {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] {D : Lettered α Q} {w : List α} {i : ℕ} {x y : Alph α i}
    (hw : D.IsHole w) (hi : 1 ≤ i) (hid : i < depth w)
    (hx : Isolated (hierOf w i) (Pset D w i) x)
    (hy : Isolated (hierOf w i) (Pset D w i) y) (hxy : x ≠ y)
    (ht : exType D w i (Pset D w i) x = exType D w i (Pset D w i) y)
    (hlen : letterWeight w i y ≤ letterWeight w i x) :
    let w' := expandTo (markOf w) i ((hierOf w i).map (identify x y))
    (NoCollapse (identify x y) (hierOf w i) ∧
      (tower D (markOf w) i).IsHole ((hierOf w i).map (identify x y)) ∧
      (∀ a ∈ hierOf w i, identify x y a ∈ hierOf w i) ∧
      (∀ a ∈ (hierOf w i).take (sCount D w i), identify x y a = a) ∧
      ∀ k, (tower D (markOf w) i).core ((hierOf w i).map (identify x y)) k =
        (tower D (markOf w) i).core (hierOf w i) k) ∧
    LevelMapResult D w i (identify x y) w' ∧ depth w' = depth w ∧
    w'.length ≤ w.length ∧ (∀ j, alphCard w' j ≤ alphCard w j) ∧ alphCard w' i < alphCard w i := by
  obtain ⟨h, hl, ha, hs⟩ := isolated_merge_spec hw hi hid hx hy hxy ht hlen
  exact ⟨Support.HoleCorrespondence.isolated_levelMap_hyps hw hx hy ht, h, h.depth_eq, hl, ha, hs⟩

/-- **Lemma (Dictionary normal form and bounded dictionaries)**, `lem:bg-dictionary`(1).
Form: A default letter defines the total hierarchy; Normal packages distinct exchange types of distinct isolated letters.
-/
theorem lem_bg_dictionary_1 {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] {D : Lettered α Q} {w : List α} (hw : D.IsHole w) :
    ∃ v, D.IsHole v ∧ depth v = depth w ∧ v.length ≤ w.length ∧
      (∀ i, sCount D v i = sCount D w i) ∧ (∀ i, alphCard v i ≤ alphCard w i) ∧ Normal D v :=
  exists_normal_form hw

/-- **Lemma (Dictionary normal form and bounded dictionaries)**, `lem:bg-dictionary`(2).
Form: Boundary propagation is the equivalent subtraction-free inequality b_i + 1 ≤ b_(i+1) + g_(i+1); normalAllowance is A(N,d). A default letter defines the total hierarchy.
-/
theorem lem_bg_dictionary_2 {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] (D : Lettered α Q) :
    (∀ w, D.IsHole w → Normal D w → ∀ d i, depth w ≤ d → 1 ≤ i → i < depth w →
      alphCard w i ≤ normalAllowance (Fintype.card Q) d + 2 * (boundaryPairs (hierOf w i)).card) ∧
    (∀ (v : List α), v ≠ [] → ∀ j, (boundaryPairs (hierOf v j)).card + 1 ≤
      (boundaryPairs (hierOf v (j + 1))).card + (hierOf v (j + 1)).toFinset.card) :=
  ⟨fun _ hw hn _ _ hd hi hid => normalAt_alphCard_le hw (hn _ hi hid) hi hid hd,
    fun _ hv => boundaryCount_step_add_one hv⟩

/-- **Lemma (Dictionary normal form and bounded dictionaries)**, `lem:bg-dictionary`(3).
Form: normalAllowance and dictionaryBound are A and G; the final existential applies to every hole of depth at most d. A default letter defines the total hierarchy.
-/
theorem lem_bg_dictionary_3 {α Q : Type*} [DecidableEq α] [Inhabited α]
    [Fintype Q] [DecidableEq Q] (D : Lettered α Q) (d : ℕ) :
    (∀ w, D.IsHole w → Normal D w → depth w ≤ d → ∀ i, 1 ≤ i → i < depth w →
      2 * (boundaryPairs (hierOf w i)).card ≤
        (normalAllowance (Fintype.card Q) d - 1) * (3 ^ (depth w - 1 - i) - 1) ∧
      alphCard w i ≤ 1 + (normalAllowance (Fintype.card Q) d - 1) * 3 ^ (depth w - 1 - i)) ∧
    (∀ w, D.IsHole w → depth w ≤ d → ∃ v, D.IsHole v ∧ depth v = depth w ∧
      v.length ≤ w.length ∧ ∀ i, 1 ≤ i → i ≤ depth v → alphCard v i ≤ dictionaryBound (Fintype.card Q) d) :=
  ⟨fun _ hw hn hd _ hi hid => ⟨normal_boundary_count_le hw hn hd hi hid,
    normal_alphCard_le hw hn hd hi hid⟩, fun _ hw hd => exists_bounded_dictionary_hole hw hd⟩

/-- **Lemma (Unary words)**, `lem:bg-unary`. -/
theorem lem_bg_unary {Γ Q : Type*} [Fintype Q] (D : Lettered Γ Q) (z : Γ) (m : ℕ)
    (hm : D.IsHole (List.replicate m z)) :
    ∃ m', 1 ≤ m' ∧ m' ≤ Fintype.card Q ∧ D.IsHole (List.replicate m' z) :=
  (exists_unary_hole_iff D z).mp ⟨m, hm⟩

/-- **Lemma (Column shortening)**, `lem:bg-columns`.
Form: Tuples are Fin k indexed; a supported letter map expresses the replacement, whose Agree field records injectivity and preservation of all derived-monitor tables; terminal-summary bits are retained explicitly. Deletion is stated for a factorization at the two cuts. Raw tuple shortening does not require marker avoidance; the supported replacement preserves avoidance when it is assumed.
-/
theorem lem_bg_columns {Γ Q : Type*} [Fintype Q] [DecidableEq Q]
    (D : Lettered Γ Q) (ℓ : Γ) (k : ℕ) :
    (∀ a b z : List (Fin k → Option Γ), Packets.Valid (a ++ b ++ z) →
      (colDFA D ℓ k).eval a = (colDFA D ℓ k).eval (a ++ b) →
      Packets.Valid (a ++ z) ∧
        summ D ℓ k (Packets.dec (a ++ z)) = summ D ℓ k (Packets.dec (a ++ b ++ z))) ∧
    (∀ Ws : Fin k → List Γ, ∃ Ws' : Fin k → List Γ,
      (∀ a, (Ws' a).Sublist (Ws a)) ∧ (∀ a, (Ws' a).length < colBound (Fintype.card Q) k) ∧
      summ D ℓ k Ws' = summ D ℓ k Ws) ∧
    (∀ E : List (List Γ), E.length ≤ k → (∀ X ∈ E, ℓ ∉ X) →
      ∃ ρ : List Γ → List Γ, Agree (der D ℓ) (der D ℓ) ρ E ∧
        (∀ X ∈ E, (ρ X).Sublist X ∧ (ρ X).length < colBound (Fintype.card Q) k ∧ ℓ ∉ ρ X ∧
          ∀ c d, (∃ p ≤ (ρ X).length, D.Λf (zlab D ℓ c (ρ X) p) (some (d, ℓ))) ↔
            ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (d, ℓ))) ∧
        (∀ v, (∀ X ∈ v, X ∈ E) → (der D ℓ).IsHole v → (der D ℓ).IsHole (v.map ρ)) ∧
        (∀ v, IsUnary v → IsUnary (v.map ρ))) := by
  refine ⟨Support.HoleCorrespondence.delete_columns D ℓ k, exists_short_tuple D ℓ k, ?_⟩
  intro E hk ha
  obtain ⟨ρ, hρ, hs⟩ := Support.HoleCorrespondence.short_letters_summary D ℓ k E hk
  exact ⟨ρ, hρ, fun X hX => ⟨(hs X hX).1, (hs X hX).2.1,
      (fun hm => ha X hX ((hs X hX).1.subset hm)), (hs X hX).2.2⟩,
    fun _ hv hh => (hρ.isHole_iff hv).mpr hh, fun _ => Support.HoleCorrespondence.unary_map ρ⟩

/-- **Lemma (Agreement under derivation)**, `lem:bg-agreement`.
Form: Finite supports and families are lists; the conclusion explicitly includes avoidance of the mapped marker. Agreement under derivation also holds for infinite state carriers.
-/
theorem lem_bg_agreement {Γ Γ' Q : Type*} {D : Lettered Γ Q} {D' : Lettered Γ' Q}
    {ρ : Γ → Γ'} {E : List Γ} (h : Agree D D' ρ E) {ℓ : Γ} (hℓ : ℓ ∈ E)
    (F : List (List Γ)) (hF : ∀ X ∈ F, ∀ a ∈ X, a ∈ E) (ha : ∀ X ∈ F, ℓ ∉ X) :
    Agree (der D ℓ) (der D' (ρ ℓ)) (List.map ρ) F ∧ ∀ X ∈ F, ρ ℓ ∉ X.map ρ :=
  ⟨h.derive hℓ F hF, fun X hX => Support.HoleCorrespondence.avoids_map h hℓ (hF X hX) (ha X hX)⟩

/-- **Lemma (Supported simultaneous compression)**, `lem:bg-compression`.
Form: E is a duplicate-free list of supported level-j letters; PositiveDictionaryBound, Agree and Admissible package dictionary bounds, all-state agreement with injectivity, and recursive marker validity. descentFactor N d g is col(N+d+1,g). The recursion is explicit: supports Es h with Es j = E, shortenings tau h from column shortening and level maps rho h, with rho (h+1) X = (tau h X).map (rho h) and the new marker of level h equal to the image of the old one under rho h, at every level h below j. A default letter defines the total hierarchy.
-/
theorem lem_bg_compression {α Q : Type*} [DecidableEq α] [Inhabited α] [Fintype Q]
    (D : Lettered α Q) {w : List α} (hw : w ≠ []) {d g j : ℕ}
    (hj : j ≤ d) (hg : PositiveDictionaryBound w j g)
    (E : List (Alph α j)) (hE : E.Nodup) (hsub : ∀ x ∈ E, x ∈ hierOf w j) :
    ∃ (ℓ' : (i : ℕ) → Alph α i) (ρ : (h : ℕ) → Alph α h → Alph α h)
      (Es : (h : ℕ) → List (Alph α h)) (τ : (h : ℕ) → Alph α (h + 1) → Alph α (h + 1)),
      Es j = E ∧
      Agree (tower D (markOf w) j) (tower D ℓ' j) (ρ j) E ∧ Admissible ℓ' j (E.map (ρ j)) ∧
      (∀ x ∈ E, (expandTo ℓ' j [ρ j x]).length ≤ descentFactor (Fintype.card Q) d g ^ j) ∧
      ∀ h < j, (Es h).Nodup ∧
        (∀ a, a ∈ Es h ↔ a = markOf w h ∨ ∃ X ∈ Es (h + 1), a ∈ τ h X) ∧
        (∀ a ∈ Es h, a ∈ hierOf w h) ∧
        Agree (tower D (markOf w) (h + 1)) (tower D (markOf w) (h + 1)) (τ h) (Es (h + 1)) ∧
        (∀ X ∈ Es (h + 1), (τ h X).Sublist X ∧
          (τ h X).length < colBound (Fintype.card Q + h) g ∧
          ρ (h + 1) X = (τ h X).map (ρ h)) ∧
        ℓ' h = ρ h (markOf w h) :=
  Support.HoleCorrespondence.shorten_level_traced D hw hj hg E hE hsub

/-- **Lemma (Elementary estimate)**, `lem:bg-estimate`.
Form: dictionaryExponent is Xi, dictionaryBound is G, and holeLengthBound N is lengthBound N d_N; the estimates hold even at N = 0.
-/
theorem lem_bg_estimate (N d : ℕ) :
    dictionaryBound N d ≤ 2 ^ dictionaryExponent N d ∧
    lengthBound N d ≤ 2 ^ 2 ^ (5 * dictionaryExponent N d + 3) ∧
    holeLengthBound N ≤ 2 ^ 2 ^ (1280 * (N + 1) ^ 5) :=
  ⟨dictionaryBound_le N d, lengthBound_le N d, holeLengthBound_le N⟩

end DeciENSSE.Paper
