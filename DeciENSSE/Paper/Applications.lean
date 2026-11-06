import DeciENSSE.Examples.Subsumption

/-! # Paper contract: Constrained Types and Simplification

Contract entries for the section *Constrained Types and Simplification* (`sec:ap`) and its
appendix (`app:ap`): the subsumption formula, the decision of subsumption, and the three
worked examples.

Only library results and logical packaging are used below. The expressions of a scheme with
free variables `F` and bound variables `B` are `Term n (F ⊕ B)`, or `BFTerm n (F ⊕ B)` over
`{⊥, f}`, so the bound variables are apart from each other and from the free ones by
construction. A tree class is a predicate on trees; over `{⊥, f}` it is a class of top-free
trees, read at the covariant variance. Decidability is a computable definition built from
the public deciders. Arrow types have arity two and the variance `Examples.arrow`.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Flattening Scheme

variable {n : ℕ} {P F B₁ B₂ : Type*} [DecidableEq P]

/-- **Proposition (Subsumption formula)**, `prop:ap-subsumption`(1).
Form: The consequent, the conjunction of C_1 and R_12, is Scheme.subsumptionGoal, whose context part ranges over the common domain, which is Dom Gamma_1 here; the class C is an arbitrary predicate on trees. For the bottom-constructor signature, instantiate C with the top-free trees of the intended class; the variable carriers need not be finite.
-/
theorem prop_ap_subsumption_1 (C : Tree n → Prop) (c : Fin n → Bool) :
    (∀ (S₁ : Scheme P (Term n (F ⊕ B₁))) (S₂ : Scheme P (Term n (F ⊕ B₂))),
      S₁.context.keys ⊆ S₂.context.keys →
        (SubsumesIn C c S₁ S₂ ↔
          ExistsEntailsTermIn C c S₂.constraint (subsumptionGoal S₁ S₂))) ∧
    (∀ (S₁ : Scheme P (BFTerm n (F ⊕ B₁))) (S₂ : Scheme P (BFTerm n (F ⊕ B₂))),
      S₁.context.keys ⊆ S₂.context.keys →
        (SubsumesIn C (fun _ => false) (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm) ↔
          ExistsEntailsTermIn C (fun _ => false)
            (S₂.constraint.map (TermLit.map BFTerm.toTerm))
            ((bfSubsumptionGoal S₁ S₂).map (TermLit.map BFTerm.toTerm)))) :=
  ⟨fun _ _ hdom => subsumesIn_iff hdom, fun _ _ hdom => subsumesTopFreeIn_iff hdom⟩

/-- **Proposition (Subsumption formula)**, `prop:ap-subsumption`(2).
Form: The class C is an arbitrary predicate on trees; a solution of C_2 assigns the free variables and the bound variables of S_2. For the bottom-constructor signature, instantiate C with the top-free trees of the intended class; the variable carriers need not be finite.
-/
theorem prop_ap_subsumption_2 (C : Tree n → Prop) (c : Fin n → Bool) :
    (∀ (S₁ : Scheme P (Term n (F ⊕ B₁))) (S₂ : Scheme P (Term n (F ⊕ B₂))),
      ¬ S₁.context.keys ⊆ S₂.context.keys →
        (SubsumesIn C c S₁ S₂ ↔
          ¬ ∃ μ : F ⊕ B₂ → Tree n, (∀ v, C (μ v)) ∧ TermSat c μ S₂.constraint)) ∧
    (∀ (S₁ : Scheme P (BFTerm n (F ⊕ B₁))) (S₂ : Scheme P (BFTerm n (F ⊕ B₂))),
      ¬ S₁.context.keys ⊆ S₂.context.keys →
        (SubsumesIn C (fun _ => false) (S₁.map BFTerm.toTerm) (S₂.map BFTerm.toTerm) ↔
          ¬ ∃ μ : F ⊕ B₂ → Tree n, (∀ v, C (μ v)) ∧
            TermSat (fun _ => false) μ (S₂.constraint.map (TermLit.map BFTerm.toTerm)))) :=
  ⟨fun _ _ hdom => subsumesIn_iff_of_not_subset hdom,
    fun _ _ hdom => subsumesIn_iff_of_not_subset (by simpa using hdom)⟩

/-- **Corollary (Deciding subsumption)**, `cor:ap-decidable`.
Form: Decidability is a computable pair of triples of the public deciders, over the full signature at every variance (arrow types are n = 2 with Examples.arrow) and over the bottom-constructor signature; the agreement of regular and arbitrary trees, for both signatures, is the propositional component.
-/
def cor_ap_decidable [Fintype F] [DecidableEq F] [Fintype B₁] [DecidableEq B₁] [Fintype B₂]
    [DecidableEq B₂] (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) (T₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (T₂ : Scheme P (BFTerm n (F ⊕ B₂))) :
    (Decidable (Subsumes c S₁ S₂) × Decidable (SubsumesReg c S₁ S₂) ×
      Decidable (SubsumesFin c S₁ S₂)) ×'
    (Decidable (SubsumesTopFree T₁ T₂) × Decidable (SubsumesTopFreeReg T₁ T₂) ×
      Decidable (SubsumesTopFreeFin T₁ T₂)) ×'
    ((SubsumesReg c S₁ S₂ ↔ Subsumes c S₁ S₂) ∧
      (SubsumesTopFreeReg T₁ T₂ ↔ SubsumesTopFree T₁ T₂)) :=
  ⟨⟨decideSubsumes c S₁ S₂, decideSubsumesReg c S₁ S₂, decideSubsumesFin c S₁ S₂⟩,
    ⟨decideSubsumesTopFree T₁ T₂, decideSubsumesTopFreeReg T₁ T₂,
      decideSubsumesTopFreeFin T₁ T₂⟩,
    subsumesReg_iff c S₁ S₂, subsumesTopFreeReg_iff T₁ T₂⟩

section Examples

open Examples

/-- **Example (Two identity schemes)**, `ex:ap-identity`.
Form: Both schemes have no free variables and empty contexts; the claims hold for every predicate C on trees, without closure assumptions. The parity claim is about the flattened consequent of S_1 ≤ S_2.
-/
theorem ex_ap_identity (P : Type*) [DecidableEq P] (C : Tree 2 → Prop) :
    (SubsumesIn C arrow (Identity.S₁ P) (Identity.S₂ P) ↔
      ExistsEntailsTermIn C arrow Identity.ante₁₂ Identity.cons₁₂) ∧
    ExistsEntailsTermIn C arrow Identity.ante₁₂ Identity.cons₁₂ ∧
    (SubsumesIn C arrow (Identity.S₂ P) (Identity.S₁ P) ↔
      ExistsEntailsTermIn C arrow [] Identity.cons₂₁) ∧
    ExistsEntailsTermIn C arrow [] Identity.cons₂₁ ∧
    (SubsumesIn C arrow (Identity.S₁ P) (Identity.S₂ P) ∧
      SubsumesIn C arrow (Identity.S₂ P) (Identity.S₁ P)) ∧
    ∀ π, ¬ IsParityAssignment arrow
      (flattenCons (Y := Name Identity.ante₁₂) Identity.cons₁₂) π :=
  ⟨Identity.formula₁₂ P C, Identity.entails₁₂ C, Identity.formula₂₁ P C, Identity.entails₂₁ C,
    Identity.equivalent P C, Identity.flattened_not_parity⟩

/-- **Example (A missed redundant constraint)**, `ex:ap-pottier`.
Form: The class D is closed under the constants and the constructor. Proving k ≤ a through the lower bound means entailing that k is below the arrow from a to the bottom tree; the signed literals are SignedC at the signed variables a+ = nu_0 a and a- = nu_1 a.
-/
theorem ex_ap_pottier {D : Tree 2 → Prop} (hD : TermClosed D) :
    ExistsEntailsTermIn (Z := Empty) D arrow Pottier.C [.le Pottier.k (.var (.inl 0))] ∧
    ExistsEntailsTermIn (Z := Fin 1) D arrow Pottier.C
      [.le Pottier.k (.var (.inr 0)), .le (.var (.inr 0)) (.var (.inl 0))] ∧
    TermSat arrow (fun _ => Tree.top) Pottier.C ∧
    (∀ t, Tree.Le arrow Pottier.kT (tarr t Tree.bot) ↔ Tree.Le arrow t Pottier.gT) ∧
    ¬ ExistsEntailsTermIn (Z := Empty) D arrow Pottier.C [.le (.var (.inl 0)) Pottier.g] ∧
    ¬ ExistsEntailsTermIn (Z := Empty) D arrow Pottier.C
      [.le Pottier.k (arr (.var (.inl 0)) .bot)] ∧
    (∀ π, ¬ IsParityAssignment arrow (flatten Pottier.C) π) ∧
    (∀ t, Tree.Le arrow (tarr t Tree.bot) t ↔
      Pottier.SignedC (Pottier.ν false t) (Pottier.ν true t)) ∧
    Pottier.SignedC Pottier.F Tree.bot ∧
    (∀ t, ¬ (Pottier.ν false t = Pottier.F ∧ Pottier.ν true t = Tree.bot)) ∧
    (∀ t, Tree.Le arrow Pottier.kT t ↔ Pottier.ν false Pottier.kT ≤ Pottier.ν false t) ∧
    Pottier.ν false Pottier.kT = tarr Pottier.F Tree.bot ∧
    ¬ Pottier.ν false Pottier.kT ≤ Pottier.F :=
  ⟨Pottier.entails D, Pottier.entails_exists hD, Pottier.top_sat, Pottier.le_lower_iff,
    Pottier.not_entails_le_g hD.top, Pottier.not_entails_lower hD.top,
    Pottier.flattened_not_parity, Pottier.signed_iff, Pottier.decoupled_sat,
    Pottier.decoupled_not_coupled, Pottier.le_iff_signed, Pottier.normalize_kT,
    Pottier.decoupled_violates⟩

/-- **Example (Merging the variables of self-application)**, `ex:ap-selfapp`.
Form: The class C is closed under the constants and the constructor; the two schemes have no free variables and empty contexts.
-/
theorem ex_ap_selfapp (P : Type*) [DecidableEq P] {C : Tree 2 → Prop} (hC : TermClosed C) :
    (SubsumesIn C arrow (SelfApp.S P) (SelfApp.S' P) ↔
      ExistsEntailsTermIn C arrow SelfApp.ante SelfApp.cons) ∧
    ExistsEntailsTermIn C arrow SelfApp.ante SelfApp.cons ∧
    (SubsumesIn C arrow (SelfApp.S' P) (SelfApp.S P) ↔
      ExistsEntailsTermIn C arrow SelfApp.ante' SelfApp.cons') ∧
    (∀ a b γ : Tree 2,
      Tree.Le arrow (tarr γ γ) (tarr a b) ↔ Tree.Le arrow a γ ∧ Tree.Le arrow γ b) ∧
    Tree.Le arrow (tarr Tree.top Tree.bot) (tarr (tarr Tree.top Tree.bot) Tree.bot) ∧
    (∀ γ : Tree 2, ¬ (Tree.Le arrow (tarr Tree.top Tree.bot) γ ∧ Tree.Le arrow γ Tree.bot)) ∧
    ¬ ExistsEntailsTermIn C arrow SelfApp.ante' SelfApp.cons' ∧
    SubsumesIn C arrow (SelfApp.S P) (SelfApp.S' P) ∧
    ¬ SubsumesIn C arrow (SelfApp.S' P) (SelfApp.S P) ∧
    ∀ η : Empty → Tree 2,
      (SelfApp.S P).IsInstance C arrow η ((SelfApp.S P).inst SelfApp.countermodel) ∧
      ((SelfApp.S P).inst SelfApp.countermodel).type =
        tarr (tarr Tree.top Tree.bot) Tree.bot ∧
      ∀ I, (SelfApp.S' P).IsInstance C arrow η I →
        ¬ I.Le arrow ((SelfApp.S P).inst SelfApp.countermodel) :=
  ⟨SelfApp.formula P C, SelfApp.entails C, SelfApp.formula' P C, SelfApp.between_iff,
    SelfApp.countermodel_sat, SelfApp.no_between, SelfApp.not_entails hC, SelfApp.subsumes P C,
    SelfApp.not_subsumes P hC, SelfApp.instance_above_none P hC⟩

end Examples

end DeciENSSE.Paper
