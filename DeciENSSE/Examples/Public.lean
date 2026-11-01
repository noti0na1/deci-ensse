import DeciENSSE.NSSE

/-! # Examples of the public interface

Small instances of the public semantics, proved by hand, and evaluations of the deciders in
the kernel at arity zero. A hidden variable can name a common bound of visible trees, as in
the binary example below, and a hidden unary fixed point separates arbitrary and regular
trees from finite trees.

## Main declarations

- `hiddenExtension`: a satisfiable antecedent with a hidden extension.
- `not_existsEntails_unconstrained_eqTop`: an unconstrained visible tree need not be top.
- `subtree_entails`, `subtree_not_entails`: the binary example `x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)`,
  which says that every subtree of `x` lies below `y`.
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

/-- The antecedent `x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` entails the consequent, with the witness
`z = x`: `x ≤ f(x, ⊥) ≤ f(x, x)`. -/
theorem subtree_entails :
    ExistsEntails (fun _ => false) subtreeAntecedent subtreeBound := by
  intro ρ hs
  have hxy : Tree.Le (fun _ => false) (ρ 0) (ρ 1) := hs (.le 0 1) (by simp [subtreeAntecedent])
  have hxf : Tree.Le (fun _ => false) (ρ 0) (DeciNSSE.Tree.node (ρ ∘ ![0, 2])) :=
    hs (.leF 0 ![0, 2]) (by simp [subtreeAntecedent])
  have hb : ρ 2 = Tree.bot := hs (.eqBot 2) (by simp [subtreeAntecedent])
  have hff : Tree.Le (fun _ => false) (DeciNSSE.Tree.node (ρ ∘ ![0, 2]))
      (DeciNSSE.Tree.node fun _ => ρ 0) := by
    simp [Fin.forall_fin_two, hb]
  refine ⟨fun _ => ρ 0, ?_⟩
  simp only [ESat, subtreeBound, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    ELit.holds, join, Fin.addCases_left, Fin.addCases_right, Function.comp_def]
  exact ⟨treeLe_refl _ _, hxy, treeLe_trans hxf hff, fun _ h => h.elim⟩

/-- The tree `f(f(⊥, f(⊥, ⊥)), ⊥)`; its left subtree is not below it. -/
def subtreeWitness : Tree 2 :=
  DeciNSSE.Tree.node ![DeciNSSE.Tree.node ![Tree.bot, DeciNSSE.Tree.node fun _ => Tree.bot],
    Tree.bot]

/-- The antecedent `x ≤ y` alone does not entail the consequent: at
`x = y = f(f(⊥, f(⊥, ⊥)), ⊥)` the witness must be `z = x`, which is not below `f(z, z)`. -/
theorem subtree_not_entails :
    ¬ ExistsEntails (fun _ => false) [.le 0 1] subtreeBound := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => subtreeWitness) (by simp [ESat, ELit.holds, treeLe_refl])
  have h1 := hs (.le (Fin.castAdd 1 0) (Fin.natAdd 3 0)) (by simp [subtreeBound])
  have h2 := hs (.le (Fin.natAdd 3 0) (Fin.castAdd 1 1)) (by simp [subtreeBound])
  have h3 := hs (.leF (Fin.natAdd 3 0) fun _ => Fin.natAdd 3 0) (by simp [subtreeBound])
  simp only [ELit.holds, join, Fin.addCases_left, Fin.addCases_right, Function.comp_def]
    at h1 h2 h3
  rw [← treeLe_antisymm h1 h2] at h3
  simp [subtreeWitness, Fin.forall_fin_two] at h3

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
