import DeciENSSE.Examples.Public

/-! # The shift closure in the introduction

For the binary covariant constructor, `shift_iff_subtrees` proves the equivalence
before `ex:intro-shift`, and `shift_iff_suffixes` gives its language formulation.
`shiftClosure` realizes the suffix closure of the constructor positions using the
library's prefix-set representation. `shiftClosure_lub` states its least-upper-bound
property, even against upper bounds containing top; `shiftClosure_least_witness`
proves the least-witness claim in the text accompanying the figure.

`subtreeBot` uses bottom at absent paths, exactly as in the paper. The equivalence
requires top-free `x` (and the language version top-free `y`), as in the paper's
`{⊥, f}` setting. It is false for unrestricted `x = y = ⊤`, as recorded by
`shift_top_counterexample`. Here `≤` is the library's covariant order, equivalent
to `Tree.Le (fun _ => false)`; `shift_iff_subtrees_variance` states that spelling.

`phiThree_not_entails` and `phiThree_not_entails_topFree` prove the remaining
antecedent in `ex:intro-shift`, using `subtreeWitness` and `subtree_no_witness` of
`Examples.Public`. Since the public constraint syntax is flat, the nested ground bound
in φ₃ is stated directly in the antecedent's semantics.

Supporting declarations track the same claims: `subtreeBot_positions` is the
left-residual identity; `subtreeBot_topFree` and `topFree_cobs` connect it to the
signature and position representation. `shiftClosure_topFree`,
`shiftClosure_positions`, and `shiftClosure_closed` verify the constructed
witness; `shift_witness_bounds` proves necessity. `shift_closed_iff` formalizes
the sentence interpreting the self-bound, and `shift_iff_subtrees_full` states
the characterization for unrestricted trees, where it also requires a top-free
`x`. `subtreeWitness_positions` and `subtreeWitness_suffix_failure` check the
explicit language counterexample.
-/

namespace DeciENSSE.Examples
open DeciNSSE
open Core (PrefixSet)
open Core.Full

/-- Constructor positions `Kpos(t)`. -/
def Kpos {n : ℕ} (t : Tree n) : Set (List (Fin n)) := {w | t.fn w = some Sym.f}

/-- All suffixes, including the word itself and the empty suffix. -/
def Suf {α : Type*} (L : Set (List α)) : Set (List α) := {w | ∃ p, p ++ w ∈ L}

/-- The subtree at a path, with bottom at absent paths. -/
def subtreeBot {n : ℕ} (t : Tree n) (p : List (Fin n)) : Tree n :=
  (t.subtree p).getD Tree.bot

/-- Constructor positions of a subtree are the left residual, including absent paths. -/
theorem subtreeBot_positions {n : ℕ} (t : Tree n) (p w : List (Fin n)) :
    w ∈ Kpos (subtreeBot t p) ↔ p ++ w ∈ Kpos t := by
  cases hs : t.subtree p with
  | none =>
    have hn : ¬ (t.fn p).isSome := by
      rw [← Tree.subtree_isSome_iff, hs]
      simp
    have hw : t.fn (p ++ w) ≠ some Sym.f := by
      intro h
      exact hn (t.domain_append_left p w (by simp [h]))
    simp only [subtreeBot, hs, Option.getD_none, Kpos, Set.mem_ofPred_eq]
    cases w <;> simp_all
  | some u =>
    simp only [subtreeBot, hs, Option.getD_some, Kpos, Set.mem_ofPred_eq,
      Tree.subtree_fn hs]

/-- Taking subtrees preserves the bottom–constructor signature. -/
theorem subtreeBot_topFree {n : ℕ} {t : Tree n} (ht : TopFree t) (p : List (Fin n)) :
    TopFree (subtreeBot t p) := by
  cases hs : t.subtree p with
  | none => simp [subtreeBot, hs]
  | some u =>
    intro w
    simpa only [subtreeBot, hs, Option.getD_some, Tree.subtree_fn hs] using ht (p ++ w)

/-- For a top-free tree, the nonbottom observation is exactly a constructor position. -/
theorem topFree_cobs {n : ℕ} {t : Tree n} (ht : TopFree t) (w : List (Fin n)) :
    w ∈ (AC.cobs t).carrier ↔ w ∈ Kpos t := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Kpos]
    · exact (ht [] rfl).elim
    · simp [Kpos]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Kpos]
    · exact (ht [] rfl).elim
    · simpa [AC.cobs_node, Kpos] using ih ((TopFree.node_iff a).mp ht i)

/-- Constructor positions form a prefix set, also for trees containing top. -/
def constructorPrefix {n : ℕ} (t : Tree n) : PrefixSet n where
  carrier := Kpos t
  prefix_closed := by
    intro u v h
    cases v with
    | nil => simpa using h
    | cons i v =>
      apply (t.child_isSome_iff u i).mp
      apply t.domain_append_left (u ++ [i]) v
      simpa [List.append_assoc] using (show (t.fn (u ++ i :: v)).isSome by rw [h]; trivial)

/-- Suffix closure of a prefix set remains prefix closed. -/
def suffixPrefix {n : ℕ} (P : PrefixSet n) : PrefixSet n where
  carrier := Suf P.carrier
  prefix_closed := by
    rintro u v ⟨p, hp⟩
    exact ⟨p, P.prefix_closed (p ++ u) v (by simpa [List.append_assoc] using hp)⟩

/-- The tree whose constructors are all suffixes of constructor positions of `x`. -/
noncomputable def shiftClosure (x : Tree 2) : Tree 2 :=
  AC.realize ⟨suffixPrefix (constructorPrefix x), AC.full, fun _ => Or.inr trivial⟩

/-- The closure uses only bottom and the constructor. -/
theorem shiftClosure_topFree (x : Tree 2) : TopFree (shiftClosure x) := by
  intro w hw
  have ha : AC.aobs (shiftClosure x) w := ⟨w, List.prefix_refl w, hw⟩
  exact (AC.realize_observations _ w).2.mp ha trivial

/-- The position-set construction realizes precisely `Suf(Kpos(x))`. -/
theorem shiftClosure_positions (x : Tree 2) : Kpos (shiftClosure x) = Suf (Kpos x) := by
  ext w
  rw [← topFree_cobs (shiftClosure_topFree x), shiftClosure, AC.cobs_realize]
  rfl

/-- The closure is the join of all subtrees. Upper bounds may contain top. -/
theorem shiftClosure_lub {x : Tree 2} (hx : TopFree x) (y : Tree 2) :
    shiftClosure x ≤ y ↔ ∀ p, subtreeBot x p ≤ y := by
  have lower (p) : subtreeBot x p ≤ shiftClosure x := by
    apply TopFree.le_of_constructor_subset (subtreeBot_topFree hx p)
    intro w hw
    change w ∈ Kpos (shiftClosure x)
    rw [shiftClosure_positions]
    exact ⟨p, (subtreeBot_positions x p w).mp hw⟩
  constructor
  · exact fun h p => le_trans (lower p) h
  · intro h
    apply (AC.order_iff _ _).mpr
    constructor
    · intro w hw
      have hp := (topFree_cobs (shiftClosure_topFree x) w).mp hw
      rw [shiftClosure_positions] at hp
      obtain ⟨p, hp⟩ := hp
      exact ((AC.order_iff _ _).mp (h p)).1
        ((topFree_cobs (subtreeBot_topFree hx p) w).mpr
          ((subtreeBot_positions x p w).mpr hp))
    · intro w _
      rw [AC.cobs_dual]
      rintro ⟨p, _, hp⟩
      exact shiftClosure_topFree x p hp

/-- The constructed join is closed under shifting to a child. -/
theorem shiftClosure_closed (x : Tree 2) :
    shiftClosure x ≤ DeciNSSE.Tree.node (fun _ => shiftClosure x) := by
  apply TopFree.le_of_constructor_subset (shiftClosure_topFree x)
  intro w hw
  cases w with
  | nil => rfl
  | cons i w =>
    change w ∈ Kpos (shiftClosure x)
    change i :: w ∈ Kpos (shiftClosure x) at hw
    rw [shiftClosure_positions] at hw ⊢
    obtain ⟨p, hp⟩ := hw
    exact ⟨p ++ [i], by simpa [List.append_assoc] using hp⟩

/-- A witness bounds every subtree of its lower bound. -/
theorem shift_witness_bounds {x y z : Tree 2}
    (h : x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) :
    ∀ p, subtreeBot x p ≤ y := by
  have hz := TopFree.of_le_node h.2.2
  have hx := TopFree.mono hz h.1
  have step : ∀ i w, i :: w ∈ Kpos z → w ∈ Kpos z := by
    intro i w hw
    exact TopFree.constructor_subset_of_le ((TopFree.node_iff _).mpr (fun _ => hz))
      h.2.2 (i :: w) hw
  have strip : ∀ p w, p ++ w ∈ Kpos z → w ∈ Kpos z := by
    intro p
    induction p with
    | nil => exact fun _ hw => hw
    | cons i p ih => exact fun w hw => ih w (step i (p ++ w) hw)
  intro p
  apply le_trans _ h.2.1
  apply TopFree.le_of_constructor_subset (subtreeBot_topFree hx p)
  intro w hw
  exact strip p w (TopFree.constructor_subset_of_le hz h.1 (p ++ w)
    ((subtreeBot_positions x p w).mp hw))

/-- The equivalence before `ex:intro-shift`; `y` may even contain top. -/
theorem shift_iff_subtrees {x : Tree 2} (hx : TopFree x) (y : Tree 2) :
    (∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) ↔
      ∀ p, subtreeBot x p ≤ y := by
  constructor
  · rintro ⟨z, hz⟩
    exact shift_witness_bounds hz
  · intro h
    refine ⟨shiftClosure x, ?_, (shiftClosure_lub hx y).mpr h, shiftClosure_closed x⟩
    apply TopFree.le_of_constructor_subset hx
    intro w hw
    change w ∈ Kpos (shiftClosure x)
    rw [shiftClosure_positions]
    exact ⟨[], hw⟩

/-- For unrestricted trees the exact characterization also requires top-free `x`. -/
theorem shift_iff_subtrees_full (x y : Tree 2) :
    (∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) ↔
      TopFree x ∧ ∀ p, subtreeBot x p ≤ y := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨TopFree.mono (TopFree.of_le_node hz.2.2) hz.1, shift_witness_bounds hz⟩
  · rintro ⟨hx, h⟩
    exact (shift_iff_subtrees hx y).mpr h

/-- On top-free trees the self-bound says exactly that every subtree lies below the tree. -/
theorem shift_closed_iff {z : Tree 2} (hz : TopFree z) :
    z ≤ DeciNSSE.Tree.node (fun _ => z) ↔ ∀ p, subtreeBot z p ≤ z := by
  constructor
  · exact fun h => shift_witness_bounds ⟨le_rfl, le_rfl, h⟩
  · intro h
    obtain ⟨u, hzu, huz, hu⟩ := (shift_iff_subtrees hz z).mpr h
    rwa [le_antisymm huz hzu] at hu

/-- The same equivalence with the variance parameter written explicitly. -/
theorem shift_iff_subtrees_variance {x : Tree 2} (hx : TopFree x) (y : Tree 2) :
    (∃ z, Tree.Le (fun _ => false) x z ∧ Tree.Le (fun _ => false) z y ∧
      Tree.Le (fun _ => false) z (DeciNSSE.Tree.node (fun _ => z))) ↔
    ∀ p, Tree.Le (fun _ => false) (subtreeBot x p) y := by
  simpa only [treeLe_false_iff_le] using shift_iff_subtrees hx y

/-- The join is a witness whenever one exists, and is below every witness. -/
theorem shiftClosure_least_witness {x y : Tree 2} (hx : TopFree x)
    (he : ∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) :
    (x ≤ shiftClosure x ∧ shiftClosure x ≤ y ∧
      shiftClosure x ≤ DeciNSSE.Tree.node (fun _ => shiftClosure x)) ∧
    ∀ z, (x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) → shiftClosure x ≤ z := by
  have lower : x ≤ shiftClosure x := by
    apply TopFree.le_of_constructor_subset hx
    intro w hw
    change w ∈ Kpos (shiftClosure x)
    rw [shiftClosure_positions]
    exact ⟨[], hw⟩
  refine ⟨⟨lower, (shiftClosure_lub hx y).mpr ((shift_iff_subtrees hx y).mp he),
    shiftClosure_closed x⟩, ?_⟩
  intro z hz
  exact (shiftClosure_lub hx z).mpr (shift_witness_bounds ⟨hz.1, le_rfl, hz.2.2⟩)

/-- The language characterization in `ex:intro-shift`, over `{⊥, f}`. -/
theorem shift_iff_suffixes {x y : Tree 2} (hx : TopFree x) (hy : TopFree y) :
    (∃ z, x ≤ z ∧ z ≤ y ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) ↔ Suf (Kpos x) ⊆ Kpos y := by
  rw [shift_iff_subtrees hx, ← shiftClosure_lub hx y,
    TopFree.le_iff_constructor_subset (shiftClosure_topFree x) hy]
  change Kpos (shiftClosure x) ⊆ Kpos y ↔ _
  rw [shiftClosure_positions]

/-- The signature restriction is essential: unrestricted top falsifies the equivalence. -/
theorem shift_top_counterexample :
    (∀ p, subtreeBot (Tree.top : Tree 2) p ≤ Tree.top) ∧
    ¬ (∃ z : Tree 2, Tree.top ≤ z ∧ z ≤ Tree.top ∧ z ≤ DeciNSSE.Tree.node (fun _ => z)) := by
  refine ⟨fun _ => Tree.le_top _, ?_⟩
  rintro ⟨z, hz⟩
  have he : z = Tree.top := (Tree.top_le_iff _).mp hz.1
  exact TopFree.of_le_node hz.2.2 [] (he ▸ rfl)

/-- The paper's countermodel has precisely the positions `ε`, `0`, and `01`. -/
theorem subtreeWitness_positions :
    Kpos subtreeWitness = {[], [0], [0, 1]} := by
  ext w
  rcases w with _ | ⟨i, _ | ⟨j, _ | ⟨k, w⟩⟩⟩
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals try fin_cases k
  all_goals simp [Kpos, subtreeWitness]
  all_goals cases w <;> simp

/-- The suffix `1` witnesses the failed inclusion in the paper's countermodel. -/
theorem subtreeWitness_suffix_failure :
    [1] ∈ Suf (Kpos subtreeWitness) ∧ [1] ∉ Kpos subtreeWitness := by
  rw [subtreeWitness_positions]
  exact ⟨⟨[0], by simp⟩, by simp⟩

/-- φ₃ fails over the full signature, with the countermodel of the paper. -/
theorem phiThree_not_entails :
    ¬ (∀ ρ : V 3 → Tree 2,
      (Tree.Le (fun _ => false) (ρ 0) (ρ 1) ∧
       Tree.Le (fun _ => false) (ρ 0) subtreeWitness) →
      ∃ σ : V 1 → Tree 2, ESat (fun _ => false) (join ρ σ) subtreeBound) := by
  intro H
  obtain ⟨σ, hs⟩ := H (fun _ => subtreeWitness) ⟨treeLe_refl _ _, treeLe_refl _ _⟩
  exact subtree_no_witness σ hs

/-- φ₃ also fails in the paper's bottom–constructor signature. -/
theorem phiThree_not_entails_topFree :
    ¬ (∀ ρ : V 3 → Tree 2, (∀ v, TopFree (ρ v)) →
      (Tree.Le (fun _ => false) (ρ 0) (ρ 1) ∧
       Tree.Le (fun _ => false) (ρ 0) subtreeWitness) →
      ∃ σ : V 1 → Tree 2, (∀ v, TopFree (σ v)) ∧
        BFSat (join ρ σ) subtreeBoundTopFree) := by
  intro H
  obtain ⟨σ, _, hs⟩ := H (fun _ => subtreeWitness) (fun _ => subtreeWitness_topFree)
    ⟨treeLe_refl _ _, treeLe_refl _ _⟩
  exact subtree_no_witness σ hs

end DeciENSSE.Examples
