import DeciENSSE.Counterexamples
import DeciENSSE.Flattening

/-! # Paper contract: flattening

The contract entry for the flattening lemma (`lem:bg-flattening`) of the section
*Background*.

Only library results and logical packaging are used below. Systems of expressions are
`TermSystem` over `{⊥, f, ⊤}` and `BFTermSystem` over `{⊥, f}`. A name is the subexpression
itself, so the flattened antecedent is over `X ⊕ Name φ` and the flattened consequent over
`(X ⊕ Name φ) ⊕ (Z ⊕ Name ψ)`. Over `{⊥, f}` the values are the top-free trees of the class.
-/

namespace DeciENSSE.Paper

open DeciNSSE Core.Full Flattening

variable {n : ℕ} {X Z : Type*}

/-- **Lemma (Flattening)**, `lem:bg-flattening`.
Form: C is an arbitrary tree predicate containing the values of the input subexpressions, expressed by EvalClosed; the three standard tree classes D are specializations, stated separately. Over the bottom-constructor signature at every variance, values are top-free trees of the class and the flattened systems have no top literal. Size is the number of variable occurrences (at most 6 per symbol) and of names (at most 1 per symbol).
-/
theorem lem_bg_flattening [DecidableEq X] [DecidableEq Z] (c : Fin n → Bool)
    (φ : TermSystem n X) (ψ : TermSystem n (X ⊕ Z))
    (φ' : BFTermSystem n X) (ψ' : BFTermSystem n (X ⊕ Z)) :
    (∀ C : Tree n → Prop, EvalClosed C (names φ) → EvalClosed C (names ψ) →
      (ExistsEntailsTermIn C c φ ψ ↔ ExistsEntailsTIn C c (flatten φ) (flattenCons ψ))) ∧
    (∀ C : Tree n → Prop,
      EvalClosed (fun t => TopFree t ∧ C t) (names (φ'.map (TermLit.map BFTerm.toTerm))) →
      EvalClosed (fun t => TopFree t ∧ C t) (names (ψ'.map (TermLit.map BFTerm.toTerm))) →
      (ExistsEntailsTermIn (fun t => TopFree t ∧ C t) c
          (φ'.map (TermLit.map BFTerm.toTerm)) (ψ'.map (TermLit.map BFTerm.toTerm)) ↔
        ExistsEntailsTIn (fun t => TopFree t ∧ C t) c
          (flatten (φ'.map (TermLit.map BFTerm.toTerm)))
          (flattenCons (ψ'.map (TermLit.map BFTerm.toTerm))))) ∧
    (∀ D : CertificateTreeClass,
      (ExistsEntailsTermIn D.Holds c φ ψ ↔
        ExistsEntailsTIn D.Holds c (flatten φ) (flattenCons ψ)) ∧
      (ExistsEntailsTermIn (fun t => TopFree t ∧ D.Holds t) c
          (φ'.map (TermLit.map BFTerm.toTerm)) (ψ'.map (TermLit.map BFTerm.toTerm)) ↔
        ExistsEntailsTIn (fun t => TopFree t ∧ D.Holds t) c
          (flatten (φ'.map (TermLit.map BFTerm.toTerm)))
          (flattenCons (ψ'.map (TermLit.map BFTerm.toTerm))))) ∧
    (∀ u, LitT.top u ∉ flatten (φ'.map (TermLit.map BFTerm.toTerm))) ∧
    (∀ u, LitT.top u ∉
      flattenCons (Y := Name (φ'.map (TermLit.map BFTerm.toTerm)))
        (ψ'.map (TermLit.map BFTerm.toTerm))) ∧
    ((flatten φ).map flatSize).sum ≤ 6 * size φ ∧
    ((flattenCons (Y := Name φ) ψ).map flatSize).sum ≤ 6 * size ψ ∧
    Fintype.card (Name φ) ≤ size φ ∧ Fintype.card (Name ψ) ≤ size ψ := by
  refine ⟨fun _ hφ hψ => existsEntailsTermIn_iff_flatten hφ hψ,
    fun _ hφ hψ => existsEntailsTermIn_iff_flatten hφ hψ,
    fun D => ⟨existsEntailsTermIn_iff_flatten (D.termClosed.evalClosed _)
        (D.termClosed.evalClosed _),
      existsEntailsTermIn_iff_flatten (D.termClosed.topFree.evalClosed φ')
        (D.termClosed.topFree.evalClosed ψ')⟩,
    top_notMem_flatten φ', fun u h => ?_, flatSize_flatten_le φ, flatSize_flattenCons_le ψ,
    card_name_le φ, card_name_le ψ⟩
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | top v => exact top_notMem_flatten ψ' v hl
  | _ => cases he

end DeciENSSE.Paper
