import DeciENSSE.Core.Basic
import DeciENSSE.Core.Full.Basic
import DeciNSSE.Semantics.Characterization

/-! # Bottom-only trees and top-free trees

Constructor positions give an equivalence between bottom-only trees and trees
without top labels. This equivalence preserves order, finite and regular classes,
and existential entailment.

## Main declarations

- `bfEquivTopFree`
- `finite_iff`
- `regular_iff`
- `existsEntailsIn_bridge`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

/-- No top label at any path, including paths outside the domain. -/
def TopFree (t : DeciNSSE.Tree n) : Prop := ∀ w, t.fn w ≠ some Sym.top

/-- Extract constructor positions; valid even for trees containing top. -/
def toBF (t : DeciNSSE.Tree n) : BFTreeN n where
  K := {w | t.fn w = some Sym.f}
  prefix_closed := by
    intro u v h
    change t.fn u = some Sym.f
    cases v with
    | nil => simpa using h
    | cons i v =>
      apply t.label_eq_f_of_proper_prefix (show u.IsPrefix (u ++ i :: v) from ⟨_, rfl⟩)
      · intro he
        have := congrArg List.length he
        simp at this
      · simp_all

private noncomputable def encodeFn (t : BFTreeN n) (w : List (Fin n)) : Option Sym := by
  classical
  exact if w ∈ t.K then some Sym.f
  else if w = [] ∨ w.dropLast ∈ t.K then some Sym.bot else none

private theorem encodeFn_f (t : BFTreeN n) (w : List (Fin n)) :
    encodeFn t w = some Sym.f ↔ w ∈ t.K := by
  classical
  simp only [encodeFn]
  split <;> simp_all

private theorem encodeFn_child (t : BFTreeN n) (w : List (Fin n)) (i : Fin n) :
    (encodeFn t (w ++ [i])).isSome ↔ w ∈ t.K := by
  classical
  have hp : (w ++ [i]) ∈ t.K → w ∈ t.K := by
    intro h
    exact t.prefix_closed _ [i] (by simpa using h)
  simp only [encodeFn]
  split
  · simp_all
  · simp

/-- Restore the root and bottom frontier of a prefix-closed constructor set. -/
noncomputable def toTree (t : BFTreeN n) : DeciNSSE.Tree n where
  fn := encodeFn t
  wf := by
    constructor
    · classical
      simp only [encodeFn]
      split <;> simp
    · intro w i
      rw [encodeFn_child, encodeFn_f]

/-- Encoding constructor positions introduces no top labels. -/
theorem toTree_topFree (t : BFTreeN n) : TopFree (toTree t) := by
  classical
  intro w
  change encodeFn t w ≠ some Sym.top
  simp only [encodeFn]
  split <;> simp_all

/-- A position has constructor label exactly when it is in the prefix-closed set. -/
@[simp] theorem toTree_f (t : BFTreeN n) (w : List (Fin n)) :
    (toTree t).fn w = some Sym.f ↔ w ∈ t.K := encodeFn_f t w

/-- Extracting constructor positions after encoding recovers the bottom-only tree. -/
@[simp] theorem toBF_toTree (t : BFTreeN n) : toBF (toTree t) = t := by
  ext w
  change (toTree t).fn w = some Sym.f ↔ _
  simp

/-- Top-free trees are determined by their constructor positions. -/
theorem topFree_ext {t u : DeciNSSE.Tree n} (ht : TopFree t) (hu : TopFree u)
    (h : ∀ w, t.fn w = some Sym.f ↔ u.fn w = some Sym.f) : t = u := by
  apply DeciNSSE.Tree.ext
  funext w
  have hd : (t.fn w).isSome ↔ (u.fn w).isSome := by
    induction w using List.reverseRecOn with
    | nil => simp [t.root_isSome, u.root_isSome]
    | append_singleton w i _ => rw [t.child_isSome_iff, u.child_isSome_iff, h]
  have hf := h w
  have ht' := ht w
  have hu' := hu w
  cases he : t.fn w with
  | none => cases he' : u.fn w <;> simp_all
  | some a =>
    cases he' : u.fn w with
    | none => simp_all
    | some b => cases a <;> cases b <;> simp_all

/-- Encoding the constructor positions of a top-free tree recovers that tree. -/
@[simp] theorem toTree_toBF (t : DeciNSSE.Tree n) (ht : TopFree t) : toTree (toBF t) = t := by
  apply topFree_ext (toTree_topFree _) ht
  intro w
  simp [toBF]

/-- The equivalence between bottom-only trees and top-free trees. -/
noncomputable def bfEquivTopFree : BFTreeN n ≃ {t : DeciNSSE.Tree n // TopFree t} where
  toFun t := ⟨toTree t, toTree_topFree t⟩
  invFun t := toBF t.val
  left_inv := toBF_toTree
  right_inv t := Subtype.ext (toTree_toBF t.val t.property)

/-- Encoding bottom gives the bottom tree. -/
@[simp] theorem toTree_bot : toTree (BFTreeN.bot : BFTreeN n) = DeciNSSE.Tree.bot := by
  apply topFree_ext (toTree_topFree _) (by intro w; cases w <;> simp)
  intro w
  cases w <;> simp

/-- Encoding commutes with every constructor child. -/
@[simp] theorem toTree_node (a : Fin n → BFTreeN n) :
    toTree (BFTreeN.node a) = DeciNSSE.Tree.node (toTree ∘ a) := by
  apply topFree_ext (toTree_topFree _)
  · intro w
    cases w with
    | nil => simp
    | cons i w => exact toTree_topFree (a i) w
  · intro w
    cases w with
    | nil => simp
    | cons i w => simp

/-- Constructor inclusion implies covariant order on top-free trees. -/
theorem le_of_constructor_subset {t u : DeciNSSE.Tree n} (ht : TopFree t) (_hu : TopFree u)
    (h : ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f) : t ≤ u := by
  intro w a b ha hb
  cases a with
  | bot => exact Sym.bot_le _
  | top => exact False.elim (ht w ha)
  | f => have := h w ha; have : b = Sym.f := Option.some.inj (hb.symm.trans this)
         subst b; exact le_rfl

/-- Covariant comparison forces every lower constructor into the upper tree. -/
theorem constructor_subset_of_le {t u : DeciNSSE.Tree n} (hu : TopFree u) (h : t ≤ u) :
    ∀ w, t.fn w = some Sym.f → u.fn w = some Sym.f := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro ht
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    have he := h [] Sym.f b ht hb
    cases b with
    | bot => simp at he
    | f => exact hb
    | top => exact False.elim (hu [] hb)
  | append_singleton w i ih =>
    intro ht
    have htf : t.fn w = some Sym.f := (t.child_isSome_iff w i).mp (by simp [ht])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((u.child_isSome_iff w i).mpr (ih htf))
    have he := h (w ++ [i]) Sym.f b ht hb
    cases b with
    | bot => simp at he
    | f => exact hb
    | top => exact False.elim (hu _ hb)

/-- Encoding preserves and reflects covariant tree order. -/
@[simp] theorem toTree_le_iff (t u : BFTreeN n) : toTree t ≤ toTree u ↔ t ≤ u := by
  constructor
  · intro h w hw
    have := constructor_subset_of_le (toTree_topFree u) h w (by simpa using hw)
    simpa using this
  · intro h
    apply le_of_constructor_subset (toTree_topFree _) (toTree_topFree _)
    intro w hw
    simpa using h ((toTree_f t w).mp hw)

/-- Encoding preserves and reflects order at constant covariant variance. -/
@[simp] theorem toTree_leGen_iff (t u : BFTreeN n) :
    DeciNSSE.Tree.Le (fun _ => false) (toTree t) (toTree u) ↔ t ≤ u := by simp

/-- Literal-preserving embedding of the bottom-only language. -/
def ofLit {V : Type*} : Lit n V → LitT n V
  | .le u v => .le u v
  | .fle a u => .fle a u
  | .lef u a => .lef u a
  | .bot u => .bot u

/-- Translating a bottom-only literal preserves its satisfaction. -/
@[simp] theorem holdsT_ofLit {V : Type*} (ρ : V → BFTreeN n) (l : Lit n V) :
    HoldsT (fun _ => false) (toTree ∘ ρ) (ofLit l) ↔ l.Holds ρ := by
  have hi : Function.Injective (toTree (n := n)) := fun _ _ h => by
    have := congrArg toBF h
    simpa using this
  cases l <;> simp only [ofLit, HoldsT, Lit.Holds, Function.comp_apply, Function.comp_assoc,
    ← toTree_node, toTree_leGen_iff, ← toTree_bot, hi.eq_iff]

/-- Translating bottom-only constraints preserves their satisfaction. -/
@[simp] theorem satT_ofLit {V : Type*} (ρ : V → BFTreeN n) (χ : List (Lit n V)) :
    SatT (fun _ => false) (toTree ∘ ρ) (χ.map ofLit) ↔ DeciENSSE.Core.Sat ρ χ := by
  simp [SatT, DeciENSSE.Core.Sat]

/-- The translated formula, with top-free visible and hidden trees. -/
def ExistsEntailsTopFree {X Z : Type*}
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ExistsEntailsTIn TopFree (fun _ => false) φ ψ

/-- Transport also works for any additional class predicate on bottom-only trees. -/
theorem existsEntailsIn_bridge {X Z : Type*} (C : BFTreeN n → Prop)
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsIn C φ ψ ↔
      ExistsEntailsTIn (fun t => TopFree t ∧ C (toBF t)) (fun _ => false)
        (φ.map ofLit) (ψ.map ofLit) := by
  have comp (ρ : X → BFTreeN n) (σ : Z → BFTreeN n) :
      toTree ∘ Sum.elim ρ σ = Sum.elim (toTree ∘ ρ) (toTree ∘ σ) := by
    funext v; cases v <;> rfl
  constructor
  · intro h ρ hρ hs
    have hr : toTree ∘ (toBF ∘ ρ) = ρ := funext fun x => toTree_toBF _ (hρ x).1
    obtain ⟨σ, hσ, hsσ⟩ := h (toBF ∘ ρ) (fun x => (hρ x).2)
      ((satT_ofLit _ _).mp (hr.symm ▸ hs))
    refine ⟨toTree ∘ σ, fun z => ⟨toTree_topFree _, by simpa using hσ z⟩, ?_⟩
    have := (satT_ofLit (Sum.elim (toBF ∘ ρ) σ) ψ).mpr hsσ
    simpa only [comp, hr] using this
  · intro h ρ hρ hs
    obtain ⟨σ, hσ, hsσ⟩ := h (toTree ∘ ρ)
      (fun x => ⟨toTree_topFree _, by simpa using hρ x⟩) ((satT_ofLit _ _).mpr hs)
    refine ⟨toBF ∘ σ, fun z => (hσ z).2, ?_⟩
    have he : toTree ∘ (toBF ∘ σ) = σ := funext fun z => toTree_toBF _ (hσ z).1
    apply (satT_ofLit _ _).mp
    simpa only [comp, he] using hsσ

/-- Arbitrary bottom-only entailment equals top-free entailment. -/
theorem existsEntails_topFree_iff {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntails φ ψ ↔ ExistsEntailsTopFree (φ.map ofLit) (ψ.map ofLit) := by
  simpa only [ExistsEntails, ExistsEntailsTopFree, and_true] using
    existsEntailsIn_bridge (fun _ => True) φ ψ

/-- Finite constructor support is equivalent to a finite path-tree domain. -/
theorem finite_dom_iff (t : BFTreeN n) :
    IsFiniteTree t ↔ (Characterization.domain (toTree t)).Finite := by
  constructor
  · intro ht
    apply ((Set.finite_singleton ([] : List (Fin n))).union
      (Set.finite_iUnion fun i : Fin n => ht.image (fun w => w ++ [i]))).subset
    intro w hw
    induction w using List.reverseRecOn with
    | nil => exact Or.inl rfl
    | append_singleton w i _ =>
      right
      apply Set.mem_iUnion.mpr
      refine ⟨i, w, ?_, rfl⟩
      exact (toTree_f t w).mp (((toTree t).child_isSome_iff w i).mp hw)
  · intro ht
    apply ht.subset
    intro w hw
    show ((toTree t).fn w).isSome
    rw [(toTree_f t w).mpr hw]
    rfl

/-- Finite bottom-only trees are exactly top-free finite-term trees under the bridge. -/
theorem finite_iff (t : BFTreeN n) :
    IsFiniteTree t ↔ ∃ a : FTree n, a.toTree = toTree t := by
  rw [Characterization.toTree_range_iff, finite_dom_iff]

/-- A path subtree has the expected bottom-only residual constructor set. -/
theorem toBF_subtree {t u : DeciNSSE.Tree n} {w : List (Fin n)}
    (h : t.subtree w = some u) :
    toBF u = (toBF t).residual w := by
  ext v
  change u.fn v = some Sym.f ↔
    t.fn (w ++ v) = some Sym.f
  rw [DeciNSSE.Tree.subtree_fn h]

/-- Every subtree of a top-free tree is top-free. -/
theorem topFree_subtree {t u : DeciNSSE.Tree n} (ht : TopFree t) {w : List (Fin n)}
    (h : t.subtree w = some u) : TopFree u := by
  intro v
  rw [DeciNSSE.Tree.subtree_fn h]
  exact ht _

/-- Outside the path-tree domain, an bottom-only residual is empty. -/
theorem toBF_residual_of_absent {t : DeciNSSE.Tree n} {w : List (Fin n)}
    (h : t.subtree w = none) :
    (toBF t).residual w = BFTreeN.bot := by
  ext v
  simp only [BFTreeN.mem_bot, iff_false]
  intro hv
  have hf : t.fn (w ++ v) = some Sym.f := by
    simpa [BFTreeN.residual, toBF] using hv
  have hd := t.domain_append_left w v (by rw [hf]; rfl)
  have := (DeciNSSE.Tree.subtree_isSome_iff t w).mpr hd
  simp [h] at this

/-- Finite residual families agree with the library's finite subtree families. -/
theorem regular_subtrees_iff (t : BFTreeN n) :
    IsRegularTree t ↔ (Characterization.subtrees (toTree t)).Finite := by
  constructor
  · intro ht
    have hr : (Set.range (fun w => t.residual w)).Finite := by
      apply Set.Finite.of_finite_image (f := BFTreeN.K)
      · simpa only [← Set.range_comp, IsRegularTree, Function.comp_def] using ht
      · intro a _ b _ he; exact BFTreeN.ext he
    apply (hr.image toTree).subset
    rintro u ⟨w, hw⟩
    refine ⟨t.residual w, ⟨_, rfl⟩, ?_⟩
    have he := toBF_subtree hw
    rw [toBF_toTree] at he
    rw [← he, toTree_toBF u (topFree_subtree (toTree_topFree t) hw)]
  · intro ht
    apply ((ht.image (fun u => (toBF u).K)).union
      (Set.finite_singleton BFTreeN.bot.K)).subset
    rintro s ⟨w, rfl⟩
    cases he : (toTree t).subtree w with
    | none =>
      right
      have hz := toBF_residual_of_absent he
      simpa using congrArg BFTreeN.K hz
    | some u =>
      left
      refine ⟨u, ⟨w, he⟩, ?_⟩
      have hz := toBF_subtree he
      simpa using congrArg BFTreeN.K hz

/-- Regular bottom-only trees are exactly top-free finite-graph unfoldings. -/
theorem regular_iff (t : BFTreeN n) :
    IsRegularTree t ↔ ∃ g : RGraph n, g.unfold = toTree t := by
  rw [Characterization.unfold_range_iff, regular_subtrees_iff]

/-- Converse finite correspondence, stated on any top-free path tree. -/
theorem topFree_finite_iff (t : DeciNSSE.Tree n) (ht : TopFree t) :
    IsFiniteTree (toBF t) ↔ ∃ a : FTree n, a.toTree = t := by
  simpa [toTree_toBF t ht] using finite_iff (toBF t)

/-- Converse regular correspondence, stated on any top-free path tree. -/
theorem topFree_regular_iff (t : DeciNSSE.Tree n) (ht : TopFree t) :
    IsRegularTree (toBF t) ↔ ∃ g : RGraph n, g.unfold = t := by
  simpa [toTree_toBF t ht] using regular_iff (toBF t)

/-- Restrict both tuples to top-free finite trees, in the existing presentation image. -/
def ExistsEntailsTopFreeFin {X Z : Type*}
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ExistsEntailsTIn (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t)
    (fun _ => false) φ ψ

/-- Restrict both tuples to top-free regular unfoldings. -/
def ExistsEntailsTopFreeReg {X Z : Type*}
    (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) : Prop :=
  ExistsEntailsTIn (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t)
    (fun _ => false) φ ψ

/-- Finite bottom-only entailment equals finite top-free entailment. -/
theorem existsEntailsFin_topFree_iff {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsIn IsFiniteTree φ ψ ↔
      ExistsEntailsTopFreeFin (φ.map ofLit) (ψ.map ofLit) := by
  have hc : (fun t => TopFree t ∧ IsFiniteTree (toBF t)) =
      (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t) := by
    funext t
    apply propext
    exact ⟨fun h => ⟨h.1, (topFree_finite_iff t h.1).mp h.2⟩,
      fun h => ⟨h.1, (topFree_finite_iff t h.1).mpr h.2⟩⟩
  simpa only [ExistsEntailsTopFreeFin, hc] using existsEntailsIn_bridge IsFiniteTree φ ψ

/-- Regular bottom-only entailment equals regular top-free entailment. -/
theorem existsEntailsReg_topFree_iff {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z))) :
    ExistsEntailsIn IsRegularTree φ ψ ↔
      ExistsEntailsTopFreeReg (φ.map ofLit) (ψ.map ofLit) := by
  have hc : (fun t => TopFree t ∧ IsRegularTree (toBF t)) =
      (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t) := by
    funext t
    apply propext
    exact ⟨fun h => ⟨h.1, (topFree_regular_iff t h.1).mp h.2⟩,
      fun h => ⟨h.1, (topFree_regular_iff t h.1).mpr h.2⟩⟩
  simpa only [ExistsEntailsTopFreeReg, hc] using existsEntailsIn_bridge IsRegularTree φ ψ

/-- Transport a source decision without evaluating the classical tree encoding. -/
def decideExistsEntailsTopFree {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z)))
    [Decidable (ExistsEntails φ ψ)] :
    Decidable (ExistsEntailsTopFree (φ.map ofLit) (ψ.map ofLit)) :=
  decidable_of_iff (ExistsEntails φ ψ) (existsEntails_topFree_iff φ ψ)

/-- Regular source decisions transport through the same syntax embedding. -/
def decideExistsEntailsTopFreeReg {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z)))
    [Decidable (ExistsEntailsIn IsRegularTree φ ψ)] :
    Decidable (ExistsEntailsTopFreeReg (φ.map ofLit) (ψ.map ofLit)) :=
  decidable_of_iff (ExistsEntailsIn IsRegularTree φ ψ) (existsEntailsReg_topFree_iff φ ψ)

/-- Finite source decisions transport through the same syntax embedding. -/
def decideExistsEntailsTopFreeFin {X Z : Type*}
    (φ : List (Lit n X)) (ψ : List (Lit n (X ⊕ Z)))
    [Decidable (ExistsEntailsIn IsFiniteTree φ ψ)] :
    Decidable (ExistsEntailsTopFreeFin (φ.map ofLit) (ψ.map ofLit)) :=
  decidable_of_iff (ExistsEntailsIn IsFiniteTree φ ψ) (existsEntailsFin_topFree_iff φ ψ)

namespace BridgeExamples

/-- Constructor transport preserves every child at arity three. -/
theorem ternary_node (a b c : BFTreeN 3) :
    toTree (BFTreeN.node ![a, b, c]) = DeciNSSE.Tree.node ![toTree a, toTree b, toTree c] := by
  rw [toTree_node]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Class correspondence includes the nullary constructor as well. -/
theorem nullary_constructor_finite :
    IsFiniteTree (BFTreeN.node (Fin.elim0 : Fin 0 → BFTreeN 0)) := by
  apply (finite_iff _).mpr
  refine ⟨FTree.node Fin.elim0, ?_⟩
  rw [FTree.toTree_node, toTree_node]
  congr 1
  funext i
  exact Fin.elim0 i

/-- A ternary bottom constraint entails a visible reflexive inequality. -/
theorem ternary_entails :
    ExistsEntailsTopFree
      (([.bot ()] : List (Lit 3 Unit)).map ofLit)
      (([.le (.inl ()) (.inl ())] : List (Lit 3 (Unit ⊕ Unit))).map ofLit) := by
  apply (existsEntails_topFree_iff _ _).mp
  intro ρ _ _
  exact ⟨fun _ => BFTreeN.bot, fun _ => trivial, by simp [DeciENSSE.Core.Sat, Lit.Holds]⟩

end BridgeExamples

end DeciENSSE.Core.Full
