import DeciENSSE.Core.Mixed.SummaryFacts

/-! # Paper contract: Pushdown Summaries

Contract entries for the section *Pushdown Summaries* (`sec:sm`) and the corresponding part
of its appendix (`app:sm`): pushdown summaries and the lowest point, duality and sign
coherence, the least closure `μ`, roots and the pop bound, deadness from automaton states,
closure membership, head prefixes, and the finite searches for satisfiability and (I0).
-/
namespace DeciENSSE.Paper
open Core Core.Full Core.Mixed Core.Words
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

/-- **Lemma (Pushdown summaries)**, `lem:sm-summaries`(1).
Form: Pure moves are represented in the covariant signed system.
-/
theorem lem_sm_summaries_1 (a b : V × Bool) :
    (a, b) ∈ Automata.D (signedSys c χ) ↔
      Automata.Moves (signedSys c χ) (a, []) (b, []) := by
  exact (Automata.summaries_D (χ := signedSys c χ) (a := a) (b := b) []).trans
    (Automata.above_iff (u := []) (v := []) (σ := []))

/-- **Lemma (Pushdown summaries)**, `lem:sm-summaries`(2).
Form: Pure moves are represented in the covariant signed system.
-/
theorem lem_sm_summaries_2 {x r : V × Bool} (β : List (Fin n)) :
    r ∈ Automata.P (signedSys c χ) x β ↔
      Automata.Moves (signedSys c χ) (x, β) (r, []) := by
  exact mem_P_iff_moves β

/-- **Lemma (Pushdown summaries)**, `lem:sm-summaries`(3).
Form: Pure moves are represented in the covariant signed system.
-/
theorem lem_sm_summaries_3 (a q : V × Bool) (w : List (Fin n)) :
    a ∈ Automata.Q (signedSys c χ) q w ↔
      Automata.Moves (signedSys c χ) (a, []) (q, w) := by
  exact (Automata.summaries_Q (χ := signedSys c χ) (y := q) (a := a) w []).trans
    (Automata.above_iff (u := []) (v := w) (σ := []))

/-- **Lemma (Lowest point)**, `lem:sm-lowest-point`.
-/
theorem lem_sm_lowest_point {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c χ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.P (signedSys c χ) (p, s) (u.take i) ∩
          Automata.Q (signedSys c χ) (q, s') (t.take e)).Nonempty := by
  exact lowest_point_leaf

/-- **Lemma (Duality and sign coherence)**, `lem:sm-duality`(1).
-/
theorem lem_sm_duality_1 (a b q : V × Bool) :
    ((a, b) ∈ Automata.D (signedSys c χ) ↔
      (flipV b, flipV a) ∈ Automata.D (signedSys c χ)) ∧
    Automata.down (signedSys c χ) (flipV q) =
      (Automata.up (signedSys c χ) q).map flipEmb := ⟨D_dual, down_flip q⟩

/-- **Lemma (Duality and sign coherence)**, `lem:sm-duality`(2).
-/
theorem lem_sm_duality_2 (y : V × Bool) (w : List (Fin n)) :
    Automata.Q (signedSys c χ) (flipV y) w =
      (Automata.P (signedSys c χ) y w).map flipEmb := by
  exact Q_flip y w

/-- **Lemma (Duality and sign coherence)**, `lem:sm-duality`(3).
-/
theorem lem_sm_duality_3 (a b p q r : V × Bool) (w : List (Fin n)) :
    ((a, b) ∈ Automata.D (signedSys c χ) → a.2 = b.2) ∧
    (r ∈ Automata.P (signedSys c χ) p w → r.2 = Bool.xor p.2 (DeciNSSE.polarity c w)) ∧
    (r ∈ Automata.Q (signedSys c χ) q w → r.2 = Bool.xor q.2 (DeciNSSE.polarity c w)) := by
  refine ⟨?_, fun h => sign_coherent h, fun h => lower_sign_coherent h⟩
  intro h
  have hh := sign_coherent (w := []) (p := a.1) (s := a.2) (r := b)
    (by simpa only [Automata.P_nil, Automata.mem_up] using h)
  simpa using hh.symm

/-- **Lemma (The least closure)**, `lem:sm-mu`.
Form: The bound 4^|V| is the cardinality of the signed powerset; PF is the finite set defined by this bounded search, and it equals the set of the paper, defined with arbitrary words. The computability claim is a computable definition: membership in that set is decided by membership in PF.
-/
def lem_sm_mu (q : V × Bool) (w : List (Fin n)) :
    DecidablePred (fun r => ∃ f γ, Fact χ f ∧ r ∈ Automata.P (signedSys c χ) (f.1, f.2.1) γ) ×'
    (((q.1, q.2, w) ∈ Mu c χ ↔ ∃ e ≤ w.length,
      (Automata.Q (signedSys c χ) q (w.take e) ∩ PF c χ).Nonempty) ∧
    (∀ r, r ∈ PF c χ ↔ ∃ f γ, Fact χ f ∧ r ∈ Automata.P (signedSys c χ) (f.1, f.2.1) γ) ∧
    (∀ r, r ∈ PF c χ ↔ ∃ f ∈ factList χ,
      ∃ γ ∈ wordsUpTo (Fintype.card (Finset (V × Bool))),
        r ∈ Automata.P (signedSys c χ) (f.1, f.2.1) γ)) :=
  ⟨fun r => decidable_of_iff (r ∈ PF c χ) mem_PF,
    mu_membership, fun _ => mem_PF,
    fun _ => by simp only [PF, Finset.mem_filter, Finset.mem_univ, true_and]⟩

/-- **Lemma (Roots and the pop bound)**, `lem:sm-roots`(1).
Form: Root deadness is expanded as reachability of a forbidden root.
-/
theorem lem_sm_roots_1 {p : V × Bool} {w : List (Fin n)} {i : Fin n}
    (h : (Automata.P (signedSys c χ) p (w ++ [i])).Nonempty) :
    (∃ r ∈ Automata.P (signedSys c χ) p w,
      (∃ a, Lit.lef r a ∈ signedSys c χ) ∧
      Moves c χ (p.1, p.2, w) (r.1, r.2, []) ∧ Neg χ (r.1, r.2, [])) ∧
    (∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, w) a) := by
  obtain ⟨r, hr, ha, hm, hn⟩ := pop_root_witness h
  exact ⟨⟨r, hr, ha, hm, hn⟩, ⟨(r.1, r.2, []), hn, moves_reach hm⟩⟩

/-- **Lemma (Roots and the pop bound)**, `lem:sm-roots`(2).
Form: Root deadness is expanded as reachability of a forbidden root.
-/
theorem lem_sm_roots_2 {p : V × Bool} {w : List (Fin n)} {k j : ℕ}
    (hk : ¬ ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, w.take k) a)
    (hkj : k < j) (hj : j ≤ w.length) :
    Automata.P (signedSys c χ) p (w.take j) = ∅ := by
  exact root_cone hk hkj hj

/-- **Lemma (Roots and the pop bound)**, `lem:sm-roots`(3).
Form: Root deadness is expanded as reachability of a forbidden root.
-/
theorem lem_sm_roots_3 {p : V} {s : Bool} {u : List (Fin n)} :
    (∃ n, Neg χ n ∧ Reach c χ (p, s, u) n) ↔
      ∃ z, (Automata.P (signedSys c χ) (p, s) (u ++ z) ∩ NegDown c χ).Nonempty := by
  exact reach_neg_iff

/-- **Lemma (Roots and the pop bound)**, `lem:sm-roots`(4).
Form: Root deadness is expanded as reachability of a forbidden root.
-/
theorem lem_sm_roots_4 {p : V × Bool} {u v : List (Fin n)}
    (h : ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, u ++ v) a) :
    ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, u) a := by
  exact root_dead_prefix h

/-- **Lemma (Deadness from states)**, `lem:sm-dead-states`(1).
Form: The root-dead region is represented by the computable state predicate negReachS rather than an intersection with a set of variables.
-/
theorem lem_sm_dead_states_1 (p : V × Bool) (w : List (Fin n)) :
    (∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, w) a) ↔
      negReachS c χ (Automata.P (signedSys c χ) p w) := by
  rw [reach_neg_iff, negReachS_iff]
  simp only [upperRun_P]

/-- **Lemma (Deadness from states)**, `lem:sm-dead-states`(2).
Form: flipHitS is intersection of the flipped summary with PF.
-/
theorem lem_sm_dead_states_2 {p : V × Bool} {t : List (Fin n)} :
    (p.1, !p.2, t) ∈ Mu c χ ↔
      ∃ e ≤ t.length, flipHitS c χ (Automata.P (signedSys c χ) p (t.take e)) := by
  exact mu_flip_membership

/-- **Lemma (Deadness from states)**, `lem:sm-dead-states`(3).
Form: The support-dead region is the disjunction of negReachS and muReachS on the current state; the last disjunct is opposite-atom membership in Mu.
-/
theorem lem_sm_dead_states_3 {p : V × Bool} {u : List (Fin n)} :
    DeadT c χ p u ↔
      negReachS c χ (Automata.P (signedSys c χ) p u) ∨
      muReachS c χ (Automata.P (signedSys c χ) p u) ∨
      ∃ e ≤ u.length, flipHitS c χ (Automata.P (signedSys c χ) p (u.take e)) := by
  exact deadT_iff_state

/-- **Lemma (Deadness from states)**, `lem:sm-dead-states`(4).
-/
theorem lem_sm_dead_states_4 {p : V × Bool} {u v : List (Fin n)} :
    DeadT c χ p (u ++ v) → DeadT c χ p u := by
  exact deadT_prefix

/-- **Lemma (Deadness from states)**, `lem:sm-dead-states`(5).
Form: The computability claim for the two finite sets of signed variables is a computable definition: membership is decided by the executable procedures decideRootDeadEmpty and decideSupportDeadEmpty; root deadness is reachability of a forbidden root.
-/
def lem_sm_dead_states_5 :
    DecidablePred (fun p : V × Bool => ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, []) a) ×'
    DecidablePred (fun p : V × Bool => DeadT c χ p []) :=
  ⟨decideRootDeadEmpty c χ, decideSupportDeadEmpty c χ⟩

/-- **Theorem (Deadness)**, `thm:sm-dead`.
-/
theorem thm_sm_dead (hsat : ∃ ρ, SatT c ρ χ) (p : V × Bool) (w : List (Fin n)) :
    (¬ Live c χ (p.1, p.2, w) ↔ DeadT c χ p w ∨ ∃ i j, SelfEv c χ p w i j) ∧
    (∀ i j, SelfEv c χ p w i j →
      ∃ δ, Reach c χ (p.1, p.2, w) (p.1, !p.2, w ++ δ)) ∧
    (¬ DeadT c χ p w → (∃ δ, Reach c χ (p.1, p.2, w) (p.1, !p.2, w ++ δ)) →
      ∃ i j, SelfEv c χ p w i j) :=
  ⟨dead_iff_unit_or_self (sat_iff_mu.mp hsat), fun _ _ => selfEv_return,
    fun hd ⟨_, hr⟩ => return_selfEv_of_not_deadT hd hr⟩

/-- **Lemma (Closure membership)**, `lem:sm-membership`.
-/
theorem lem_sm_membership {p q : V} {s s' : Bool} {u t : List (Fin n)}
    (hlive : Live c χ (p, s, u)) :
    (q, s', t) ∈ Cl c χ (p, s, u) ↔ (q, s', t) ∈ Mu c χ ∨
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.P (signedSys c χ) (p, s) (u.take i) ∩
          Automata.Q (signedSys c χ) (q, s') (t.take e)).Nonempty := by
  exact cl_membership_live hlive

/-- **Lemma (Head prefixes)**, `lem:sm-head-prefix`.
Form: Root deadness is expanded as reachability of a forbidden root.
-/
theorem lem_sm_head_prefix (p : V × Bool) (γ : List (Fin n))
    (h : (Automata.P (signedSys c χ) p γ).Nonempty) (i : ℕ) (hi : i < γ.length) :
    ∃ a, Neg χ a ∧ Reach c χ (p.1, p.2, γ.take i) a :=
  reach_neg_iff.mpr ⟨[], by simpa using P_proper_prefix_neg h hi⟩

/-- **Proposition (Satisfiability and (I0))**, `prop:sm-decide`(1).
Form: Forbidden roots are enumerated by negList; MuCollision is simultaneous membership of both signs. The bound is the cardinality of the product of the two flagged powerset readers, equal to 2^(4|V|+2). Decidability of satisfiability is a computable definition, the executable procedure decideSatMixed.
-/
def prop_sm_decide_1 :
    Decidable (∃ ρ, SatT c ρ χ) ×'
    ((∃ ρ, SatT c ρ χ) ↔
      (∀ a ∈ negList χ, ¬ (Automata.down (signedSys c χ) (a.1, a.2.1) ∩ PF c χ).Nonempty) ∧
      ∀ v w, ¬ MuCollision c χ v w) ∧
    (∀ v w, MuCollision c χ v w →
      ∃ w', w'.length < muCollisionBound V ∧ MuCollision c χ v w') := by
  refine ⟨decideSatMixed c χ, ?_, fun _ _ => muCollision_short c χ⟩
  rw [sat_iff_mu, avoids_mu_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h v w hh
    obtain ⟨hp, hn⟩ := (muCollision_iff c χ v w).mp hh
    exact h (.pair v w) hp hn
  · intro h
    apply (consistent_mu_iff c χ).mpr
    exact fun v w _ => h v w

/-- **Proposition (Satisfiability and (I0))**, `prop:sm-decide`(2).
Form: FailureI0 is consequent membership and antecedent nonmembership at a visible signed atom. The bound is the cardinality of the product of the two flagged powerset readers, equal to 2^(2|X|+2|X+Z|+2). Decidability of (I0) is a computable definition, the executable procedure decideCondI0.
-/
def prop_sm_decide_2 {X Z : Type*} [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z))) :
    Decidable (CondI0 c φ ψ) ×'
    ((¬ CondI0 c φ ψ ↔ ∃ p w, FailureI0 c φ ψ p w) ∧
    (∀ p w, FailureI0 c φ ψ p w →
      ∃ v, v.length < condI0Bound X Z ∧ FailureI0 c φ ψ p v)) :=
  ⟨decideCondI0 c φ ψ, not_condI0_iff c φ ψ, fun _ _ => failureI0_short c φ ψ⟩
end DeciENSSE.Paper
