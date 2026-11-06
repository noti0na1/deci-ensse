import DeciENSSE.Counterexamples
import DeciENSSE.Examples.ShiftClosure
import DeciENSSE.Flattening

/-! # Paper contract: Introduction

Contract entries for the section *Introduction* (`sec:intro`): the main theorem as stated
there (`thm:intro-main`) and the running example (`ex:intro-shift`).

Only library results and logical packaging are used below. Systems of the decision claims are
systems of type expressions over finite variable types, decided after flattening; the
certificate claims are about flat systems, with `s` the number of variables after flattening.
The three tree classes are `CertificateTreeClass`. Over `{⊥, f}` the constructor is covariant
and the values are top-free trees. Decidability is a computable definition built from the
public deciders. The running example is over `{⊥, f}` with `f` binary, in the public flat
syntax with the visible variables `x = 0`, `y = 1`, `b = 2`.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Bounds

variable {n : ℕ} {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- **Theorem (Main theorem)**, `thm:intro-main`.
Form: Decidability is a computable pair of triples of the public deciders for systems of type expressions, over the full signature at every variance and over the bottom-constructor signature with f covariant. The certificate claims, for flat systems in each tree class D, are the propositional component; E3(O(s)) is E3(22s + 15), and E3(44s + 15) over the bottom-constructor signature, where the word is one of the gadget pair gadgetAnte and gadgetCons over complete lists xs and zs.
-/
def thm_intro_main (c : Fin n → Bool) (φ : TermSystem n X) (ψ : TermSystem n (X ⊕ Z))
    (φ' : BFTermSystem n X) (ψ' : BFTermSystem n (X ⊕ Z)) :
    (Decidable (ExistsEntailsTerm c φ ψ) × Decidable (ExistsEntailsTermReg c φ ψ) ×
      Decidable (ExistsEntailsTermFin c φ ψ)) ×'
    (Decidable (ExistsEntailsTermTopFree φ' ψ') × Decidable (ExistsEntailsTermTopFreeReg φ' ψ') ×
      Decidable (ExistsEntailsTermTopFreeFin φ' ψ')) ×'
    ∀ D : CertificateTreeClass,
    (∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))),
      SatisfiableIn D.Holds c φ → SatisfiableIn D.Holds c ψ →
      ¬ ExistsEntailsTIn D.Holds c φ ψ →
      (∃ k, ∃ w : CounterexampleWord c φ ψ k,
        w.length ≤ E3 (22 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      ∀ k (_ : CounterexampleWord c φ ψ k),
        ∃ ρ, (∀ x, D.Holds (ρ x)) ∧ SatT c ρ φ ∧
          ¬ ∃ σ, (∀ z, D.Holds (σ z)) ∧ SatT c (Sum.elim ρ σ) ψ) ∧
    (∀ (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) (xs : List X) (zs : List Z),
      (∀ x, x ∈ xs) → (∀ z, z ∈ zs) →
      SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ →
      SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) ψ →
      ¬ ExistsEntailsTIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ ψ →
      (∃ k, ∃ w : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
          (TopFree.gadgetCons zs ψ) k,
        w.length ≤ E3 (44 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      ∀ k (_ : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
          (TopFree.gadgetCons zs ψ) k),
        ∃ ρ : X → Tree n, (∀ x, TopFree (ρ x) ∧ D.Holds (ρ x)) ∧
          SatT (fun _ => false) ρ φ ∧
          ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
            SatT (fun _ => false) (Sum.elim ρ σ) ψ) :=
  ⟨⟨decideExistsEntailsTerm c φ ψ, decideExistsEntailsTermReg c φ ψ,
      decideExistsEntailsTermFin c φ ψ⟩,
    ⟨decideExistsEntailsTermTopFree φ' ψ', decideExistsEntailsTermTopFreeReg φ' ψ',
      decideExistsEntailsTermTopFreeFin φ' ψ'⟩,
    fun D => ⟨fun _ _ hφ hψ h =>
      ⟨(exists_short_counterexampleWord D hφ hψ h).elim fun ⟨k, w, hw⟩ hb => ⟨k, w, hw.trans hb⟩,
        fun _ w => (w.countermodels_in D hφ).elim fun _ ⟨⟨ρ, hD, hs, ho⟩, hn⟩ =>
          ⟨ρ, hD, hs, fun ⟨σ, _, hσ⟩ => hn ρ ho ⟨σ, hσ⟩⟩⟩,
      fun _ _ _ _ hxs hzs hφ hψ h =>
      ⟨(exists_short_counterexampleWord_gadget D hxs hzs hφ hψ h).elim
          fun ⟨k, w, hw⟩ hb => ⟨k, w, hw.trans hb⟩,
        fun _ w => (w.gadget_countermodels hxs hzs D hφ).1⟩⟩⟩

section Example

open Examples

/-- **Example (Shift closure: the running example)**, `ex:intro-shift`.
Form: The running systems use top-free binary trees at the covariant order, with an unused visible b in phi_1 and phi_3. The subtree-position identity allows arbitrary trees; the subtree characterization requires only a top-free x; the explicit witness theorem for phi_2 also holds over the full signature. Kpos and Suf are sets of words, the shifted subtree is subtreeBot, and the nested bound of phi_3 is stated semantically.
-/
theorem ex_intro_shift :
    (∀ x y : Tree 2, TopFree x → TopFree y → (x ≤ y ↔ Kpos x ⊆ Kpos y)) ∧
    (∀ (x : Tree 2) (η w : List (Fin 2)), w ∈ Kpos (subtreeBot x η) ↔ η ++ w ∈ Kpos x) ∧
    (∀ x y : Tree 2, TopFree x →
      ((∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) ↔
        ∀ η, subtreeBot x η ≤ y)) ∧
    (∀ x y : Tree 2, TopFree x → TopFree y →
      ((∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) ↔
        Suf (Kpos x) ⊆ Kpos y)) ∧
    ¬ ExistsEntailsTopFree [.le 0 1] subtreeBoundTopFree ∧
    TopFree subtreeWitness ∧ Kpos subtreeWitness = {[], [0], [0, 1]} ∧
    ([1] ∈ Suf (Kpos subtreeWitness) ∧ [1] ∉ Kpos subtreeWitness) ∧
    ExistsEntailsTopFree subtreeAntecedentTopFree subtreeBoundTopFree ∧
    (∀ ρ : V 3 → Tree 2, ESat (fun _ => false) ρ subtreeAntecedent →
      ESat (fun _ => false) (join ρ fun _ => ρ 0) subtreeBound) ∧
    ¬ (∀ ρ : V 3 → Tree 2, (∀ v, TopFree (ρ v)) →
      (Tree.Le (fun _ => false) (ρ 0) (ρ 1) ∧
        Tree.Le (fun _ => false) (ρ 0) subtreeWitness) →
      ∃ σ : V 1 → Tree 2, (∀ v, TopFree (σ v)) ∧ BFSat (join ρ σ) subtreeBoundTopFree) :=
  ⟨fun _ _ hx hy => TopFree.le_iff_constructor_subset hx hy, subtreeBot_positions,
    fun _ y hx => shift_iff_subtrees hx y, fun _ _ hx hy => shift_iff_suffixes hx hy,
    subtree_not_entails_topFree, subtreeWitness_topFree, subtreeWitness_positions,
    subtreeWitness_suffix_failure, subtree_entails_topFree, subtree_witness,
    phiThree_not_entails_topFree⟩

end Example

end DeciENSSE.Paper
