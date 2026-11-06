import DeciNSSE.Semantics.Characterization
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order

/-! # Normalization and duality

The normalization lemma (`lem:bg-normalization`) of the paper, in the parts
that the imported library does not state: normalization of a dual, the second
order equivalence, the subtree of a normalized tree at every position, and the
preservation of domains, finiteness and regularity.

The library already provides `DeciNSSE.normalize_node` and
`DeciNSSE.normalize_true` (`ν_s f(t_i)_i = f(ν_{s ⊕ c(i)} t_i)_i` and
`ν₁ t = (ν₀ t)∂`), `DeciNSSE.normalize_involutive`, `DeciNSSE.treeLe_iff_normalize`
and `DeciNSSE.dual_le_iff`. Duality is normalization for the covariant variance
at the sign `1` (`DeciNSSE.Tree.dual`), so every statement below also covers it.

## Main declarations

- `normalize_dual`: `ν_s (t∂) = ν_{1-s} t`, in particular `ν₀ (t∂) = ν₁ t`
- `treeLe_iff_normalize_true`: `t ≤_c u ↔ ν₁ u ≤ ν₁ t`
- `subtree_normalize`: the subtree of `ν_s t` at `w` is `ν_{s ⊕ par(w)} (w⁻¹ t)`
- `domain_normalize`, `finite_domain_normalize_iff`, `finite_subtrees_normalize_iff`
-/

namespace DeciENSSE.Support
open DeciNSSE DeciNSSE.Characterization

variable {n : ℕ}

/-- **Normalization** (1) (`lem:bg-normalization`(1)). Normalizing a dual
normalizes at the opposite sign: `ν_s (t∂) = ν_{1-s} t`; in particular
`ν₀ (t∂) = ν₁ t`. -/
theorem normalize_dual (c : Fin n → Bool) (s : Bool) (t : Tree n) :
    Tree.normalize c s (Tree.dual t) = Tree.normalize c (!s) t := by
  apply Tree.ext; funext π
  cases h : t.fn π with
  | none => simp [h]
  | some a =>
    cases s <;> cases hp : polarity c π <;> cases a <;> simp [h, hp, Sym.flip]

/-- **Normalization** (2), second equivalence (`lem:bg-normalization`(2)):
`t ≤_c u` iff `ν₁ u ≤ ν₁ t`. -/
theorem treeLe_iff_normalize_true (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ Tree.normalize c true u ≤ Tree.normalize c true t := by
  rw [treeLe_iff_normalize, normalize_true, normalize_true, dual_le_iff]

/-- The polarity of a concatenation. -/
theorem polarity_append (c : Fin n → Bool) (π ρ : List (Fin n)) :
    polarity c (π ++ ρ) = Bool.xor (polarity c π) (polarity c ρ) := by
  induction π with
  | nil => simp
  | cons i π ih => simp [ih]

/-- **Normalization** (4) (`lem:bg-normalization`(4)). The subtree of `ν_s t` at
a position `w` is `ν_{s ⊕ par(w)} (w⁻¹ t)`, at every word `w`: both sides are
undefined outside the domain of `t`. -/
theorem subtree_normalize (c : Fin n → Bool) (s : Bool) (t : Tree n) (w : List (Fin n)) :
    (Tree.normalize c s t).subtree w =
      (t.subtree w).map (Tree.normalize c (Bool.xor s (polarity c w))) := by
  cases h : t.subtree w with
  | none =>
    have hn : ¬ (t.fn w).isSome := by
      rw [← Tree.subtree_isSome_iff, h]; simp
    have hn' : ¬ ((Tree.normalize c s t).subtree w).isSome := by
      rw [Tree.subtree_isSome_iff, normalize_domain]; exact hn
    exact Option.not_isSome_iff_eq_none.mp hn'
  | some u =>
    have hs : ((Tree.normalize c s t).subtree w).isSome := by
      rw [Tree.subtree_isSome_iff, normalize_domain, ← Tree.subtree_isSome_iff, h]; rfl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [hv, Option.map_some, Option.some.injEq]
    apply Tree.ext; funext ρ
    rw [Tree.subtree_fn hv, normalize_fn, normalize_fn, Tree.subtree_fn h, polarity_append,
      Bool.xor_assoc]

/-- **Normalization** (4): normalization preserves domains. -/
@[simp] theorem domain_normalize (c : Fin n → Bool) (s : Bool) (t : Tree n) :
    domain (Tree.normalize c s t) = domain t := by
  ext π; simp [domain]

/-- **Normalization** (4): normalization preserves finiteness. -/
theorem finite_domain_normalize_iff (c : Fin n → Bool) (s : Bool) (t : Tree n) :
    (domain (Tree.normalize c s t)).Finite ↔ (domain t).Finite := by
  rw [domain_normalize]

/-- The subtrees of `ν_s t` are among the trees `ν₀ t'` and `ν₁ t'` for the
subtrees `t'` of `t`. -/
theorem subtrees_normalize_subset (c : Fin n → Bool) (s : Bool) (t : Tree n) :
    subtrees (Tree.normalize c s t) ⊆
      Tree.normalize c false '' subtrees t ∪ Tree.normalize c true '' subtrees t := by
  rintro u ⟨π, hπ⟩
  rw [subtree_normalize] at hπ
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hπ
  rcases Bool.eq_false_or_eq_true (Bool.xor s (polarity c π)) with hb | hb <;> rw [hb]
  · exact Or.inr ⟨v, ⟨π, hv⟩, rfl⟩
  · exact Or.inl ⟨v, ⟨π, hv⟩, rfl⟩

/-- **Normalization** (4): normalization preserves regularity, that is,
finitely many distinct subtrees. -/
theorem finite_subtrees_normalize_iff (c : Fin n → Bool) (s : Bool) (t : Tree n) :
    (subtrees (Tree.normalize c s t)).Finite ↔ (subtrees t).Finite := by
  have h : ∀ t : Tree n, (subtrees t).Finite → (subtrees (Tree.normalize c s t)).Finite :=
    fun t ht => ((ht.image _).union (ht.image _)).subset (subtrees_normalize_subset c s t)
  refine ⟨fun ht => ?_, h t⟩
  simpa using h _ ht

end DeciENSSE.Support
