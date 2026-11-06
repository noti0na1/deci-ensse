import DeciENSSE.Core.Mixed.Conditions
import DeciENSSE.Core.Mixed.Signed

/-! # Paper contract: Signed Leaf Cones

Contract entries for the section *Signed Leaf Cones* (`sec:lf`) and its appendix (`app:lf`):
the leaf representation of trees, the clause form of systems, pure moves, least closures,
duality, moving extensions first, collision returns and the three causes of deadness.
-/
namespace DeciENSSE.Paper
open DeciNSSE Core.Full Core.Mixed
variable {n : ℕ} {V X Z : Type*} {c : Fin n → Bool} {χ : List (LitT n V)}

/-- **Theorem (Leaf representation)**, `thm:lf-representation`(1).
Form: LeafPair packages disjointness and closure under arbitrary right extensions.
-/
theorem thm_lf_representation_1 (c : Fin n → Bool) :
    (∀ t : Tree n, (∀ s, ExtensionClosed (leaf c t s)) ∧
      ∀ w, w ∈ leaf c t false → w ∈ leaf c t true → False) ∧
    ∀ L : LeafPair n, ∃! t : Tree n, ∀ s, leaf c t s = L.cone s := by
  refine ⟨fun t => ⟨leaf_extension c t, leaf_disjoint c t⟩, fun L => ?_⟩
  exact ⟨Core.Mixed.decode c L, leaf_decode c L,
    fun t ht => leaf_injective c (fun s => (ht s).trans (leaf_decode c L s).symm)⟩

/-- **Theorem (Leaf representation)**, `thm:lf-representation`(2). -/
theorem thm_lf_representation_2 (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ leaf c t false ⊆ leaf c u false ∧ leaf c u true ⊆ leaf c t true :=
  treeLe_iff_leaf c t u

/-- **Theorem (Leaf representation)**, `thm:lf-representation`(3).
Form: The four constant-cone equalities are expressed by membership for either sign.
-/
theorem thm_lf_representation_3 (c : Fin n → Bool) (t : Tree n)
    (a : Fin n → Tree n) :
    (∀ s w, (w ∈ leaf c Tree.top s ↔ s = false) ∧
      (w ∈ leaf c Tree.bot s ↔ s = true)) ∧
    (∀ s, leaf c (Tree.dual t) s = leaf c t (!s)) ∧
    (∀ s, [] ∉ leaf c (DeciNSSE.Tree.node a) s) ∧
    (∀ s i w, i :: w ∈ leaf c (DeciNSSE.Tree.node a) s ↔ w ∈ leaf c (a i) (Bool.xor s (c i))) ∧
    ([] ∈ leaf c t false ↔ t = Tree.top) ∧ ([] ∈ leaf c t true ↔ t = Tree.bot) :=
  ⟨fun s w => ⟨leaf_top c s w, leaf_bot c s w⟩, leaf_dual c t,
    leaf_node_nil c a, leaf_node_cons c a, leaf_root_plus c t, leaf_root_minus c t⟩

/-- **Lemma (Clause form)**, `lem:lf-clauses`.
Form: The singleton-system clause equivalence includes the automatic extension and exclusion conditions; uniqueness and existence express the bijection. The correspondence also holds for infinite variable carriers.
-/
theorem lem_lf_clauses (c : Fin n → Bool) (χ : List (LitT n V)) :
    (∀ (ρ : V → Tree n) (l : LitT n V), SatT c ρ [l] ↔ Sol c [l] (configSet c ρ)) ∧
    (∀ ρ : V → Tree n, SatT c ρ χ ↔ Sol c χ (configSet c ρ)) ∧
    ∀ S, Sol c χ S ↔ ∃! ρ, SatT c ρ χ ∧ configSet c ρ = S := by
  refine ⟨fun ρ _ => sat_iff_sol ρ, fun ρ => sat_iff_sol ρ, fun S => ?_⟩
  constructor
  · intro h
    obtain ⟨ρ, hρ, he⟩ := sol_iff_assignment.mp h
    exact ⟨ρ, ⟨hρ, he⟩, fun τ ht => configSet_injective (ht.2.trans he.symm)⟩
  · rintro ⟨ρ, hρ, _⟩
    exact sol_iff_assignment.mpr ⟨ρ, hρ⟩

/-- **Lemma (Pure moves)**, `lem:lf-moves`(1).
Form: Includes the stated extension to pure derivations. The variable carrier need not be finite.
-/
theorem lem_lf_moves_1 (σ : List (Fin n)) (p q : Config n V) :
    (Move c χ p q → Move c χ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ)) ∧
    (Moves c χ p q → Moves c χ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ)) :=
  ⟨move_append σ, moves_append σ⟩

/-- **Lemma (Pure moves)**, `lem:lf-moves`(2).
Form: Includes the stated sign invariant for pure derivations. The variable carrier need not be finite.
-/
theorem lem_lf_moves_2 (p q : Config n V) :
    (Move c χ p q → Bool.xor q.2.1 (polarity c q.2.2) = Bool.xor p.2.1 (polarity c p.2.2)) ∧
    (Moves c χ p q → Bool.xor q.2.1 (polarity c q.2.2) = Bool.xor p.2.1 (polarity c p.2.2)) :=
  ⟨move_sign, moves_sign⟩

/-- **Lemma (Least closures)**, `lem:lf-closure`(1).
Form: Facts, seeds, closure and leastness are separate conjuncts. The variable carrier need not be finite.
-/
theorem lem_lf_closure_1 (A : Set (Config n V)) :
    (∀ a, Fact χ a → a ∈ Hull c χ A) ∧ A ⊆ Hull c χ A ∧ Closed c χ (Hull c χ A) ∧
    ∀ S, Closed c χ S → (∀ ⦃a⦄, Fact χ a → a ∈ S) → A ⊆ S → Hull c χ A ⊆ S :=
  ⟨fun _ => hull_facts A, subset_hull A, hull_closed A, fun _ => hull_least⟩

/-- **Lemma (Least closures)**, `lem:lf-closure`(2).
Form: Consistency is Avoids paired with Consistent; the general leastness clause also applies to the empty and singleton seed sets. The variable carrier need not be finite.
-/
theorem lem_lf_closure_2 (A : Set (Config n V)) (a : Config n V) :
    ((∃ S, Sol c χ S ∧ A ⊆ S) ↔ Avoids χ (Hull c χ A) ∧ Consistent (Hull c χ A)) ∧
    (Avoids χ (Hull c χ A) → Consistent (Hull c χ A) → Sol c χ (Hull c χ A) ∧ A ⊆ Hull c χ A) ∧
    (∀ S, Sol c χ S → A ⊆ S → Hull c χ A ⊆ S) ∧
    ((∃ ρ, SatT c ρ χ) ↔ Avoids χ (Mu c χ) ∧ Consistent (Mu c χ)) ∧
    (Live c χ a ↔ Avoids χ (Cl c χ a) ∧ Consistent (Cl c χ a)) ∧
    ((∃ ρ, SatT c ρ χ) → Sol c χ (Mu c χ)) ∧
    (∀ S, Sol c χ S → Mu c χ ⊆ S) ∧
    (Live c χ a → Sol c χ (Cl c χ a)) ∧
    (∀ S, Sol c χ S → a ∈ S → Cl c χ a ⊆ S) :=
  ⟨exists_sol_superset_iff A, (fun hn hd => ⟨(hull_sol hn hd).1, (hull_sol hn hd).2.1⟩), fun _ h => hull_least h.closed h.facts,
    sat_iff_mu, live_iff, sol_mu, fun _ => mu_subset, sol_cl, fun _ => cl_subset⟩

/-- **Lemma (Least closures)**, `lem:lf-closure`(3).
Form: Consistency separates forbidden roots from exclusion pairs; Exclusion fixes the positive-first orientation. The variable carrier need not be finite.
-/
theorem lem_lf_closure_3 (A : Set (Config n V))
    (h : ¬ (Avoids χ (Hull c χ A) ∧ Consistent (Hull c χ A))) :
    ∃ x y, (Fact χ x ∨ x ∈ A) ∧ (Fact χ y ∨ y ∈ A) ∧
      ((∃ p, Reach c χ x p ∧ Neg χ p) ∨
        ∃ p q, Exclusion p q ∧ Reach c χ x p ∧ Reach c χ y q) :=
  hull_obstruction h

/-- **Lemma (Least closures)**, `lem:lf-closure`(4).
Form: The variable carrier need not be finite.
-/
theorem lem_lf_closure_4 (p : V) (s : Bool) (u α : List (Fin n)) :
    Reach c χ (p, s, u) (p, s, u ++ α) ∧
    Cl c χ (p, s, u ++ α) ⊆ Cl c χ (p, s, u) ∧
    (Live c χ (p, s, u) → Live c χ (p, s, u ++ α)) :=
  ⟨reach_extend p s u α, cl_extend_subset p s u α, live_extend α⟩

/-- **Lemma (Least closures)**, `lem:lf-closure`(5).
Form: Sum types separate visible and hidden variables; consistency is Avoids paired with Consistent. The equivalence holds for every seed set, without the paper's redundant closure assumptions. Visible and hidden carriers may be infinite.
-/
theorem lem_lf_closure_5 (S : Set (Config n X)) (ψ : List (LitT n (X ⊕ Z))) :
    (S ∈ Projected c ψ ↔ Avoids ψ (Hull c ψ (visible '' S)) ∧
      Consistent (Hull c ψ (visible '' S)) ∧ restrict (Hull c ψ (visible '' S)) = S) ∧
    (S ∈ Projected c ψ → Sol c ψ (Hull c ψ (visible '' S))) ∧
    (∀ T, Sol c ψ T → restrict T = S → Hull c ψ (visible '' S) ⊆ T) :=
  ⟨projected_iff_hull S ψ,
    fun h => (hull_sol ((projected_iff_hull S ψ).mp h).1 ((projected_iff_hull S ψ).mp h).2.1).1,
    fun _ => hull_least_projected⟩

/-- **Lemma (Duality)**, `lem:lf-duality`.
Form: The variable carrier need not be finite.
-/
theorem lem_lf_duality (a b : Config n V) :
    (Move c χ a b → Move c χ (flipC b) (flipC a)) ∧
    (Moves c χ a b → Moves c χ (flipC b) (flipC a)) :=
  ⟨move_dual, moves_dual⟩

/-- **Lemma (Extensions first)**, `lem:lf-ext-first`.
Form: The variable carrier need not be finite.
-/
theorem lem_lf_ext_first (p : V) (s : Bool) (u : List (Fin n)) (b : Config n V) :
    Reach c χ (p, s, u) b ↔ ∃ α, Moves c χ (p, s, u ++ α) b :=
  reach_iff_moves

/-- **Lemma (Extensions first)**, `lem:lf-extensions`.
Form: The variable carrier need not be finite.
-/
theorem lem_lf_extensions (p : V) (s : Bool) (u : List (Fin n)) (b : Config n V) :
    Reach c χ (p, s, u) b ↔ ∃ α, Moves c χ (p, s, u ++ α) b :=
  reach_iff_moves

/-- **Lemma (Collision return)**, `lem:lf-collision`.
Form: The variable carrier need not be finite.
-/
theorem lem_lf_collision (p q h : V) (s t r : Bool) (u v w : List (Fin n))
    (h₁ : Reach c χ (p, s, u) (h, r, w)) (h₂ : Reach c χ (q, t, v) (h, !r, w)) :
    (∃ δ, Reach c χ (p, s, u) (q, !t, v ++ δ)) ∧
    ∃ α δ, Moves c χ (p, s, u ++ α) (q, !t, v ++ δ) := by
  obtain ⟨δ, hd⟩ := collision_return h₁ h₂
  obtain ⟨α, ha⟩ := reach_iff_moves.mp hd
  exact ⟨⟨δ, hd⟩, ⟨α, δ, ha⟩⟩

/-- **Corollary (Deadness)**, `cor:lf-dead`(1).
Form: This item states sufficiency of cause (a) and its pure form; the full disjunction equivalence is in item (3). The variable carrier need not be finite.
-/
theorem cor_lf_dead_1 (hs : ∃ ρ, SatT c ρ χ) (p : V) (s : Bool) (u : List (Fin n)) :
    ((∃ e, Neg χ e ∧ Reach c χ (p, s, u) e) → ¬ Live c χ (p, s, u)) ∧
    ((∃ e, Neg χ e ∧ Reach c χ (p, s, u) e) ↔
      ∃ α e, Neg χ e ∧ Moves c χ (p, s, u ++ α) e) := by
  refine ⟨fun h => (dead_iff (sat_iff_mu.mp hs)).mpr (Or.inl h), ?_⟩
  constructor
  · rintro ⟨e, he, hr⟩
    obtain ⟨α, ha⟩ := reach_iff_moves.mp hr
    exact ⟨α, e, he, ha⟩
  · rintro ⟨α, e, he, ha⟩
    exact ⟨e, he, reach_iff_moves.mpr ⟨α, ha⟩⟩

/-- **Corollary (Deadness)**, `cor:lf-dead`(2).
Form: This item states sufficiency of cause (b); the full disjunction equivalence is in item (3). The variable carrier need not be finite.
-/
theorem cor_lf_dead_2 (hs : ∃ ρ, SatT c ρ χ) (p : V) (s : Bool) (u : List (Fin n))
    (h : ∃ δ, (p, !s, u ++ δ) ∈ Mu c χ) : ¬ Live c χ (p, s, u) :=
  (dead_iff (sat_iff_mu.mp hs)).mpr (Or.inr (Or.inl h))

/-- **Corollary (Deadness)**, `cor:lf-dead`(3).
Form: Includes the full three-cause equivalence and the pure form of cause (c). The variable carrier need not be finite.
-/
theorem cor_lf_dead_3 (hs : ∃ ρ, SatT c ρ χ) (p : V) (s : Bool) (u : List (Fin n)) :
    (¬ Live c χ (p, s, u) ↔
      (∃ e, Neg χ e ∧ Reach c χ (p, s, u) e) ∨
      (∃ δ, (p, !s, u ++ δ) ∈ Mu c χ) ∨
      (∃ δ, Reach c χ (p, s, u) (p, !s, u ++ δ))) ∧
    ((∃ δ, Reach c χ (p, s, u) (p, !s, u ++ δ)) ↔
      ∃ α δ, Moves c χ (p, s, u ++ α) (p, !s, u ++ δ)) := by
  refine ⟨dead_iff (sat_iff_mu.mp hs), ?_⟩
  constructor
  · rintro ⟨δ, hr⟩
    obtain ⟨α, ha⟩ := reach_iff_moves.mp hr
    exact ⟨α, δ, ha⟩
  · rintro ⟨α, δ, ha⟩
    exact ⟨δ, reach_iff_moves.mpr ⟨α, ha⟩⟩

end DeciENSSE.Paper
