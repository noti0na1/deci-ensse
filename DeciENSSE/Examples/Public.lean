import DeciENSSE.NSSE
import DeciENSSE.TopFree

/-! # Examples of the public interface

Small instances of the public semantics, proved by hand, and evaluations of the deciders in
the kernel at arity zero. A hidden variable can name a common bound of visible trees, as in
the binary example below, and a hidden unary fixed point separates arbitrary and regular
trees from finite trees.

## Main declarations

- `hiddenExtension`: a satisfiable antecedent with a hidden extension.
- `not_existsEntails_unconstrained_eqTop`: an unconstrained visible tree need not be top.
- `subtree_entails`, `subtree_not_entails`: the binary example `x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)`,
  which says that every subtree of `x` lies below `y`; `subtree_entails_topFree` and
  `subtree_not_entails_topFree` state the same over `{⊥, f}`.
- `children_entails_topFree` (and its regular and finite versions), `children_not_entails`,
  `gadget_needs_covariance`: the gadget is needed on every visible variable, and it needs
  covariance.
- `unaryCycle_classes`: a hidden unary fixed point exists precisely in the two
  classes admitting infinite trees.
- `nullary_yes`, `nullary_no`, `nullary_topFree_yes`, `nullary_topFree_no`: deciders evaluated
  in the kernel at arity zero.
-/

namespace DeciENSSE.Examples
open DeciNSSE

/-! ## A hidden bottom and an unconstrained visible tree -/

/-- A bottom antecedent has a solution, for every arity and variance. -/
theorem antecedent_satisfiable {n : ℕ} (c : Fin n → Bool) :
    ∃ ρ : V 1 → Tree n, ESat c ρ [.eqBot 0] :=
  ⟨fun _ => Tree.bot, by simp [ESat, ELit.holds]⟩

/-- Bottom witnesses the hidden inequality, including at arity zero. -/
theorem hiddenExtension {n : ℕ} (c : Fin n → Bool) :
    ExistsEntails (k := 1) (h := 1) c [.eqBot 0]
      [.le (Fin.castAdd 1 0) (Fin.natAdd 1 0),
       .leF (Fin.natAdd 1 0) (fun _ => Fin.natAdd 1 0)] := by
  intro ρ hs
  have hρ : ρ 0 = Tree.bot := hs (.eqBot 0) (by simp)
  refine ⟨fun _ => Tree.bot, ?_⟩
  simp only [ESat, List.mem_cons, forall_eq_or_imp,
    ELit.holds, join, Fin.addCases_left, Fin.addCases_right, hρ]
  simp

/-- Empty constraints are satisfiable. -/
theorem empty_satisfiable {n k : ℕ} (c : Fin n → Bool) :
    ∃ ρ : V k → Tree n, ESat c ρ [] :=
  ⟨fun _ => Tree.bot, by simp [ESat]⟩

/-- Hidden choices cannot force an unconstrained visible tree to be top. -/
theorem not_existsEntails_unconstrained_eqTop {n : ℕ} (c : Fin n → Bool) :
    ¬ ExistsEntails (k := 1) (h := 1) c [] [.eqTop (Fin.castAdd 1 0)] := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => Tree.bot) (by simp [ESat])
  have h := hs (.eqTop (Fin.castAdd 1 0)) (by simp)
  simp only [ELit.holds, join, Fin.addCases_left] at h
  exact Tree.bot_ne_top h

/-! ## A binary example

For a binary covariant constructor, the literal `z ≤ f(z, z)` puts every subtree of `z`
below `z`, so `∃ z. x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)` holds exactly when every subtree of `x`
lies below `y`. -/

/-- The consequent `x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)` for a binary constructor, with the visible
variables `x = 0`, `y = 1`, `b = 2` and the hidden variable `z`. -/
def subtreeBound : EConstraint 2 (3 + 1) :=
  [.le (Fin.castAdd 1 0) (Fin.natAdd 3 0), .le (Fin.natAdd 3 0) (Fin.castAdd 1 1),
   .leF (Fin.natAdd 3 0) fun _ => Fin.natAdd 3 0]

/-- The antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥`. -/
def subtreeAntecedent : EConstraint 2 3 := [.le 0 1, .leF 0 ![0, 2], .eqBot 2]

/-- The witness `z = x` for the antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥`:
`x ≤ f(x, ⊥) ≤ f(x, x)`. -/
theorem subtree_witness (ρ : V 3 → Tree 2) (hs : ESat (fun _ => false) ρ subtreeAntecedent) :
    ESat (fun _ => false) (join ρ fun _ => ρ 0) subtreeBound := by
  have hxy : Tree.Le (fun _ => false) (ρ 0) (ρ 1) := hs (.le 0 1) (by simp [subtreeAntecedent])
  have hxf : Tree.Le (fun _ => false) (ρ 0) (DeciNSSE.Tree.node (ρ ∘ ![0, 2])) :=
    hs (.leF 0 ![0, 2]) (by simp [subtreeAntecedent])
  have hb : ρ 2 = Tree.bot := hs (.eqBot 2) (by simp [subtreeAntecedent])
  have hff : Tree.Le (fun _ => false) (DeciNSSE.Tree.node (ρ ∘ ![0, 2]))
      (DeciNSSE.Tree.node fun _ => ρ 0) := by
    simp [Fin.forall_fin_two, hb]
  simp only [ESat, subtreeBound, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    ELit.holds, join, Fin.addCases_left, Fin.addCases_right, Function.comp_def]
  exact ⟨treeLe_refl _ _, hxy, treeLe_trans hxf hff, fun _ h => h.elim⟩

/-- The antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` entails the consequent, with the witness
`z = x`: `x ≤ f(x, ⊥) ≤ f(x, x)`. -/
theorem subtree_entails :
    ExistsEntails (fun _ => false) subtreeAntecedent subtreeBound :=
  fun ρ hs => ⟨fun _ => ρ 0, subtree_witness ρ hs⟩

/-- The tree `f(f(⊥, f(⊥, ⊥)), ⊥)`; its left subtree is not below it. -/
def subtreeWitness : Tree 2 :=
  DeciNSSE.Tree.node ![DeciNSSE.Tree.node ![Tree.bot, DeciNSSE.Tree.node fun _ => Tree.bot],
    Tree.bot]

/-- At `x = y = f(f(⊥, f(⊥, ⊥)), ⊥)` the consequent has no witness: it must be `z = x`,
which is not below `f(z, z)`. -/
theorem subtree_no_witness (σ : V 1 → Tree 2) :
    ¬ ESat (fun _ => false) (join (fun _ => subtreeWitness) σ) subtreeBound := by
  intro hs
  have h1 := hs (.le (Fin.castAdd 1 0) (Fin.natAdd 3 0)) (by simp [subtreeBound])
  have h2 := hs (.le (Fin.natAdd 3 0) (Fin.castAdd 1 1)) (by simp [subtreeBound])
  have h3 := hs (.leF (Fin.natAdd 3 0) fun _ => Fin.natAdd 3 0) (by simp [subtreeBound])
  simp only [ELit.holds, join, Fin.addCases_left, Fin.addCases_right, Function.comp_def]
    at h1 h2 h3
  rw [← treeLe_antisymm h1 h2] at h3
  simp [subtreeWitness, Fin.forall_fin_two] at h3

/-- The antecedent `x ≤ y` alone does not entail the consequent: at
`x = y = f(f(⊥, f(⊥, ⊥)), ⊥)` the witness must be `z = x`, which is not below `f(z, z)`. -/
theorem subtree_not_entails :
    ¬ ExistsEntails (fun _ => false) [.le 0 1] subtreeBound := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => subtreeWitness) (by simp [ESat, ELit.holds, treeLe_refl])
  exact subtree_no_witness σ hs

/-! ## The binary example over `{⊥, f}`

The running example of the paper is stated over `{⊥, f}`. Both claims hold there as well:
the witness `z = x` and the countermodel `f(f(⊥, f(⊥, ⊥)), ⊥)` are top-free. -/

/-- The consequent `x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)` over `{⊥, f}`. -/
def subtreeBoundTopFree : BFConstraint 2 (3 + 1) :=
  [.le (Fin.castAdd 1 0) (Fin.natAdd 3 0), .le (Fin.natAdd 3 0) (Fin.castAdd 1 1),
   .leF (Fin.natAdd 3 0) fun _ => Fin.natAdd 3 0]

/-- The antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` over `{⊥, f}`. -/
def subtreeAntecedentTopFree : BFConstraint 2 3 := [.le 0 1, .leF 0 ![0, 2], .eqBot 2]

/-- Over `{⊥, f}` the antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` entails the consequent, with
the top-free witness `z = x`. -/
theorem subtree_entails_topFree :
    ExistsEntailsTopFree subtreeAntecedentTopFree subtreeBoundTopFree :=
  fun ρ hρ hs => ⟨fun _ => ρ 0, fun _ => hρ 0, subtree_witness ρ hs⟩

/-- The countermodel `f(f(⊥, f(⊥, ⊥)), ⊥)` is top-free. -/
theorem subtreeWitness_topFree : TopFree subtreeWitness := by
  simp [subtreeWitness, TopFree.node_iff, Fin.forall_fin_two]

/-- Over `{⊥, f}` the antecedent `x ≤ y` alone does not entail the consequent. -/
theorem subtree_not_entails_topFree :
    ¬ ExistsEntailsTopFree [.le 0 1] subtreeBoundTopFree := by
  intro H
  obtain ⟨σ, -, hs⟩ := H (fun _ => subtreeWitness) (fun _ => subtreeWitness_topFree)
    (by simp [BFSat, BFLit.toELit, ESat, ELit.holds, treeLe_refl])
  exact subtree_no_witness σ hs

/-! ## Both requirements on the gadget

Over `{⊥, f}` the consequent `x ≤ f(z₀, …, z_{n-1})`, with `x` visible, holds for the empty
antecedent in every tree class: take the children of `x`, or `⊥` if `x = ⊥`. Over `{⊥, f, ⊤}`
it fails at `x = ⊤`, for every variance, so the gadget must also be placed on visible
variables that do not occur in the antecedent. The gadget also needs covariance: with a
contravariant argument, `y ≤ f(y, …, y)` holds for a tree `y` with a label `⊤`. -/

/-- The consequent `x ≤ f(z₀, …, z_{n-1})`, with one visible and `n` hidden variables. -/
def childrenBound (n : ℕ) : BFConstraint n (1 + n) := [.leF (Fin.castAdd n 0) (Fin.natAdd 1)]

/-- Over `{⊥, f}` the children of `x` witness `x ≤ f(z₀, …, z_{n-1})`. -/
theorem children_entails_topFree (n : ℕ) :
    ExistsEntailsTopFree (k := 1) [] (childrenBound n) := by
  intro ρ hρ _
  rcases (ρ 0).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩
  · refine ⟨fun _ => Tree.bot, fun _ => TopFree.bot, ?_⟩
    simp [BFSat, childrenBound, BFLit.toELit, ESat, ELit.holds, join, h]
  · exact absurd (h ▸ hρ 0 []) (by simp)
  · refine ⟨a, (TopFree.node_iff a).mp (h ▸ hρ 0), ?_⟩
    simp [BFSat, childrenBound, BFLit.toELit, ESat, ELit.holds, join, h, Function.comp_def]

/-- The same over regular trees, by `existsEntailsTopFreeReg_iff`. -/
theorem children_entails_topFreeReg (n : ℕ) :
    ExistsEntailsTopFreeReg (k := 1) [] (childrenBound n) :=
  (existsEntailsTopFreeReg_iff _ _).mpr (children_entails_topFree n)

/-- The same over finite trees: the children of a finite term are finite terms. -/
theorem children_entails_topFreeFin (n : ℕ) :
    ExistsEntailsTopFreeFin (k := 1) [] (childrenBound n) := by
  intro ρ hρ _
  have hx := hρ 0
  cases h : ρ 0 with
  | bot =>
    refine ⟨fun _ => FTree.bot, fun _ => TopFree.bot, ?_⟩
    simp [BFSat, childrenBound, BFLit.toELit, ESat, ELit.holds, join, h]
  | top => rw [h] at hx; exact absurd (hx []) (by simp)
  | node a =>
    rw [h, FTree.toTree_node] at hx
    refine ⟨a, (TopFree.node_iff _).mp hx, ?_⟩
    simp [BFSat, childrenBound, BFLit.toELit, ESat, ELit.holds, join, h, Function.comp_def]

/-- Over `{⊥, f, ⊤}` the same consequent fails at `x = ⊤`, for every variance. -/
theorem children_not_entails (n : ℕ) (c : Fin n → Bool) :
    ¬ ExistsEntails (k := 1) c [] ((childrenBound n).map BFLit.toELit) := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => Tree.top) (by simp [ESat])
  have h := hs _ (List.mem_singleton_self _)
  simp [BFLit.toELit, ELit.holds, join] at h

/-- With a contravariant argument `j`, the tree `y = f(t₀, …, t_{n-1})` with `tᵢ = ⊤` at the
contravariant and `tᵢ = ⊥` at the covariant arguments satisfies `y ≤ f(y, …, y)` but has a
label `⊤`; for the arrow, `y = ⊤ → ⊥` and `y ≤ y → y`. -/
theorem gadget_needs_covariance {n : ℕ} (c : Fin n → Bool) (j : Fin n) (hj : c j = true) :
    Tree.Le c (DeciNSSE.Tree.node fun i => if c i then Tree.top else Tree.bot)
        (DeciNSSE.Tree.node fun _ =>
          DeciNSSE.Tree.node fun i => if c i then Tree.top else Tree.bot) ∧
      ¬ TopFree (DeciNSSE.Tree.node fun i => if c i then Tree.top else Tree.bot) := by
  refine ⟨?_, fun h => h [j] (by simp [hj])⟩
  rw [node_treeLe_node_iff]
  intro i
  by_cases hi : c i <;> simp [hi]

/-! ## A hidden unary fixed point -/

/-- A hidden unary equation, expressed by its two inequalities. -/
def unaryCycle : EConstraint 1 (1 + 1) :=
  [.leF (Fin.natAdd 1 0) (fun _ => Fin.natAdd 1 0),
   .fLe (fun _ => Fin.natAdd 1 0) (Fin.natAdd 1 0)]

private theorem unaryCycle_sat (c : Fin 1 → Bool) (ρ : V 1 → Tree 1) :
    ESat c (join ρ (fun _ : V 1 => (RGraph.allF 1).unfold)) unaryCycle := by
  have h := RGraph.allF_unfold_node (n := 1)
  simp only [ESat, unaryCycle, List.mem_cons, forall_eq_or_imp,
    ELit.holds, join, Fin.addCases_right, Function.comp_def]
  rw [← h]
  simp [treeLe_refl]

/-- The all-constructor infinite tree witnesses the unary cycle. -/
theorem unaryCycle_entails (c : Fin 1 → Bool) :
    ExistsEntails (k := 1) (h := 1) c [] unaryCycle := by
  intro ρ _
  exact ⟨fun _ => (RGraph.allF 1).unfold, unaryCycle_sat c ρ⟩

/-- A one-state graph witnesses the unary cycle. -/
theorem unaryCycle_entailsReg (c : Fin 1 → Bool) :
    ExistsEntailsReg (k := 1) (h := 1) c [] unaryCycle := by
  intro ρ _
  exact ⟨fun _ => RGraph.allF 1, unaryCycle_sat c _⟩

private theorem unary_finite_not_fixed (a : FTree 1) :
    a.toTree ≠ DeciNSSE.Tree.node (fun _ => a.toTree) := by
  induction a with
  | bot => simp
  | top => simp
  | node a ih =>
    intro h
    have hc := congrFun ((DeciNSSE.Tree.node_eq_node_iff _ _).mp h) 0
    apply ih 0
    calc
      (a 0).toTree = DeciNSSE.Tree.node (fun i => (a i).toTree) := hc
      _ = DeciNSSE.Tree.node (fun _ => (a 0).toTree) := by
        congr 1
        funext i
        rw [Subsingleton.elim i (0 : Fin 1)]

/-- No finite term equals its own unary constructor. -/
theorem unaryCycle_not_entailsFin (c : Fin 1 → Bool) :
    ¬ ExistsEntailsFin (k := 1) (h := 1) c [] unaryCycle := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => FTree.bot) (by simp [ESat])
  have hlo := hs (.leF (Fin.natAdd 1 0) (fun _ => Fin.natAdd 1 0)) (by simp [unaryCycle])
  have hhi := hs (.fLe (fun _ => Fin.natAdd 1 0) (Fin.natAdd 1 0)) (by simp [unaryCycle])
  simp only [ELit.holds, join, Fin.addCases_right, Function.comp_def] at hlo hhi
  exact unary_finite_not_fixed (σ 0) (treeLe_antisymm hlo hhi)

/-- The same satisfiable antecedent separates finite from arbitrary and regular entailment. -/
theorem unaryCycle_classes (c : Fin 1 → Bool) :
    ExistsEntails (k := 1) (h := 1) c [] unaryCycle ∧
      ExistsEntailsReg (k := 1) (h := 1) c [] unaryCycle ∧
      ¬ ExistsEntailsFin (k := 1) (h := 1) c [] unaryCycle :=
  ⟨unaryCycle_entails c, unaryCycle_entailsReg c, unaryCycle_not_entailsFin c⟩

/-! ## Kernel evaluation at arity zero -/

/-- At arity zero an unconstrained visible assignment admits a hidden bottom. -/
theorem nullary_yes :
    @decide _ (decideExistsEntails (k := 0) (h := 1) Fin.elim0 [] [.eqBot 0]) = true :=
  by decide +kernel

/-- A visible bottom cannot also be top, even if a hidden variable is available. -/
theorem nullary_no :
    @decide _ (decideExistsEntails (k := 1) (h := 1) Fin.elim0 [.eqBot 0]
      [.eqTop 0]) = false := by decide +kernel

/-- The bottom–constructor nullary procedure also finds a hidden bottom. -/
theorem nullary_topFree_yes :
    @decide _ (decideExistsEntailsTopFree (n := 0) (k := 0) (h := 1) [] [.eqBot 0]) = true :=
  by decide +kernel

/-- In the bottom–constructor signature a hidden variable cannot be both `⊥` and above
`f()`. -/
theorem nullary_topFree_no :
    @decide _ (decideExistsEntailsTopFree (n := 0) (k := 0) (h := 1) []
      [.eqBot 0, .fLe Fin.elim0 0]) = false := by decide +kernel

end DeciENSSE.Examples
