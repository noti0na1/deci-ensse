import DeciENSSE.NSSE

/-! # Small existential entailment examples

The antecedents below have explicit solutions. A unary hidden fixed point
separates arbitrary and regular trees from finite trees.

## Main declarations

- `hiddenExtension`: a satisfiable antecedent with a hidden extension.
- `noInstance`: an unconstrained visible tree need not be top.
- `unaryCycle_classes`: a hidden unary fixed point exists precisely in the two
  classes admitting infinite trees.
-/

namespace DeciENSSE.Examples
open DeciNSSE

/-- A bottom antecedent has a solution, for every arity and variance. -/
theorem antecedent_satisfiable {n : ℕ} (c : Fin n → Bool) :
    ∃ ρ : V 1 → Tree n, ESat c ρ [.eqBot 0] :=
  ⟨fun _ => Tree.bot, by simp [ESat, ELit.holds]⟩

/-- Bottom witnesses the hidden inequality, including at arity zero. -/
theorem hiddenExtension {n : ℕ} (c : Fin n → Bool) :
    ExistsEntailsAny (k := 1) (h := 1) c [.eqBot 0]
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
theorem noInstance {n : ℕ} (c : Fin n → Bool) :
    ¬ ExistsEntailsAny (k := 1) (h := 1) c [] [.eqTop (Fin.castAdd 1 0)] := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => Tree.bot) (by simp [ESat])
  have h := hs (.eqTop (Fin.castAdd 1 0)) (by simp)
  simp only [ELit.holds, join, Fin.addCases_left] at h
  exact Tree.bot_ne_top h

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
    ExistsEntailsAny (k := 1) (h := 1) c [] unaryCycle := by
  intro ρ _
  exact ⟨fun _ => (RGraph.allF 1).unfold, unaryCycle_sat c ρ⟩

/-- A one-state graph witnesses the unary cycle. -/
theorem unaryCycle_entailsReg (c : Fin 1 → Bool) :
    ExistsEntailsAnyReg (k := 1) (h := 1) c [] unaryCycle := by
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
    ¬ ExistsEntailsAnyFin (k := 1) (h := 1) c [] unaryCycle := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => FTree.bot) (by simp [ESat])
  have hlo := hs (.leF (Fin.natAdd 1 0) (fun _ => Fin.natAdd 1 0)) (by simp [unaryCycle])
  have hhi := hs (.fLe (fun _ => Fin.natAdd 1 0) (Fin.natAdd 1 0)) (by simp [unaryCycle])
  simp only [ELit.holds, join, Fin.addCases_right, Function.comp_def] at hlo hhi
  exact unary_finite_not_fixed (σ 0) (treeLe_antisymm hlo hhi)

/-- The same satisfiable antecedent separates finite from arbitrary and regular entailment. -/
theorem unaryCycle_classes (c : Fin 1 → Bool) :
    ExistsEntailsAny (k := 1) (h := 1) c [] unaryCycle ∧
      ExistsEntailsAnyReg (k := 1) (h := 1) c [] unaryCycle ∧
      ¬ ExistsEntailsAnyFin (k := 1) (h := 1) c [] unaryCycle :=
  ⟨unaryCycle_entails c, unaryCycle_entailsReg c, unaryCycle_not_entailsFin c⟩

/-- At arity zero an unconstrained visible assignment admits a hidden bottom. -/
theorem nullary_yes :
    @decide _ (decideExistsEntailsAny (k := 0) (h := 1) Fin.elim0 [] [.eqBot 0]) = true :=
  by decide +kernel

/-- A visible bottom cannot also be top, even if a hidden variable is available. -/
theorem nullary_no :
    @decide _ (decideExistsEntailsAny (k := 1) (h := 1) Fin.elim0 [.eqBot 0]
      [.eqTop 0]) = false := by decide +kernel

/-- The bottom–constructor nullary procedure also finds a hidden bottom. -/
theorem nullary_topFree_yes :
    @decide _ (decideExistsEntails (n := 0) (k := 0) (h := 1) [] [.eqBot 0]) = true :=
  by decide +kernel

/-- The bottom–constructor nullary procedure rejects a hidden bottom constructor. -/
theorem nullary_topFree_no :
    @decide _ (decideExistsEntails (n := 0) (k := 0) (h := 1) []
      [.eqBot 0, .fLe Fin.elim0 0]) = false := by decide +kernel

end DeciENSSE.Examples
