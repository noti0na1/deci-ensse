import DeciENSSE.Core.Mixed.Membership
import DeciENSSE.Core.Words.Self.SS2Self

/-! # Extracted mixed instances with negative-unit enrichment

The signed readers form self-aware two-word instances whose holes are
exactly the failures of the remaining mixed entailment condition.

## Main declarations

- `extractS`, `extractS_fh`, `extractS_isHoleS_iff`,
  `condII_iff_no_holes`, `mixed_reduction`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Full
variable {n : ℕ}
variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Finite, executable extraction sharing the unit reader. -/
def extractS (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (p q : X × Bool) : SS2Self (Fin n) (Finset (X × Bool)) (TargetState X Z)
      (Finset ((X ⊕ Z) × Bool)) (Finset ((X ⊕ Z) × Bool)) where
  A := Bound.lower (signedSys c φ) q
  B := targetDFA c φ ψ p
  A' := Bound.lower (signedSys c ψ) (.inl q.1, q.2)
  B' := Bound.upper (signedSys c ψ) (.inl p.1, p.2)
  Bad := Finset.univ.filter fun Q => (Q ∩ PF c φ).Nonempty
  Rej := targetRej c φ ψ
  Guard := Finset.univ.filter fun S => (S.1 ∩ S.2.1).Nonempty
  Head := Finset.univ.filter fun S => (S.1 ∩ S.2).Nonempty
  SelfGuard := targetSelfGuard

variable {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
variable (p q : X × Bool)

/-- The lower spine run. -/
theorem extractS_A_atCut (t : List (Fin n)) (e : ℕ) :
    (extractS c φ ψ p q).A.atCut t e = Bound.Q (signedSys c φ) q (t.take e) := rfl

/-- Both upper runs and the sticky past-hit flag (also valid beyond the last cut). -/
theorem extractS_B_atCut (u : List (Fin n)) (j : ℕ) :
    ((extractS c φ ψ p q).B.atCut u j).1 = Bound.P (signedSys c φ) p (u.take j) ∧
    (((extractS c φ ψ p q).B.atCut u j).2.1 = true ↔
      ∃ e ≤ min j u.length, flipHitS c φ (Bound.P (signedSys c φ) p (u.take e))) ∧
    ((extractS c φ ψ p q).B.atCut u j).2.2 =
      Bound.P (signedSys c ψ) (.inl p.1, p.2) (u.take j) := targetDFA_atCut p u j

/-- The head readers record consequent lower and upper prefix summaries. -/
theorem extractS_head_atCut (t u : List (Fin n)) (e i : ℕ) :
    (extractS c φ ψ p q).A'.atCut t e =
      Bound.Q (signedSys c ψ) (.inl q.1, q.2) (t.take e) ∧
    (extractS c φ ψ p q).B'.atCut u i =
      Bound.P (signedSys c ψ) (.inl p.1, p.2) (u.take i) := ⟨rfl, rfl⟩

/-- The extracted guard is an antecedent upper/lower summary intersection. -/
theorem extractS_guard_iff (t u : List (Fin n)) (e i : ℕ) :
    ((extractS c φ ψ p q).A.atCut t e, (extractS c φ ψ p q).B.atCut u i) ∈
      (extractS c φ ψ p q).Guard ↔
    (Bound.P (signedSys c φ) p (u.take i) ∩
      Bound.Q (signedSys c φ) q (t.take e)).Nonempty := by
  simp only [extractS, Finset.mem_filter, Finset.mem_univ, true_and,
    Bound.lower_atCut, (targetDFA_atCut p u i).1, Finset.inter_comm]

/-- Extracted rejection excludes both kinds of unit deadness. -/
theorem extractS_rej_iff (u : List (Fin n)) (j : ℕ) :
    (extractS c φ ψ p q).B.atCut u j ∈ (extractS c φ ψ p q).Rej ↔
      ¬ DeadT c φ p (u.take j) ∧ ¬ DeadU c ψ p (u.take j) :=
  targetDFA_rej_atCut p u j

/-- Both support languages are prefix closed, hence rejection persists. -/
theorem extractS_J_isSome (u : List (Fin n)) :
    ((extractS c φ ψ p q).J u).isSome = true ↔
      ¬ DeadT c φ p u ∧ ¬ DeadU c ψ p u := by
  constructor
  · intro h
    cases hj : (extractS c φ ψ p q).J u with
    | none => simp [hj] at h
    | some j =>
      obtain ⟨hr, _, _⟩ := ((extractS c φ ψ p q).J_eq_some_iff u j).mp hj
      obtain ⟨ht, hu⟩ := (extractS_rej_iff p q u j).mp hr
      constructor
      · intro hd
        exact ht (deadT_prefix (u := u.take j) (v := u.drop j) (by simpa using hd))
      · intro hd
        exact hu (deadU_prefix (u := u.take j) (v := u.drop j) (by simpa using hd))
  · intro h
    cases hj : (extractS c φ ψ p q).J u with
    | some j => simp
    | none =>
      have hn := ((extractS c φ ψ p q).J_eq_none_iff u).mp hj u.length le_rfl
      exact False.elim (hn ((extractS_rej_iff p q u u.length).mpr (by simpa using h)))

/-- The raw first rejection ignores the consequent negative-unit enrichment. -/
def extractRawJ (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))
    (p : X × Bool) (u : List (Fin n)) : Option ℕ :=
  (List.range (u.length + 1)).find? fun e =>
    decide (¬ targetDeadT c φ ((targetDFA c φ ψ p).atCut u e))

/-- The raw cut is the first prefix without antecedent unit deadness. -/
theorem extractRawJ_eq_some_iff (u : List (Fin n)) (j : ℕ) :
    extractRawJ c φ ψ p u = some j ↔
      ¬ DeadT c φ p (u.take j) ∧ j ≤ u.length ∧
        ∀ i < j, DeadT c φ p (u.take i) := by
  classical
  simp only [extractRawJ, List.find?_range_eq_some, Bool.not_eq_true_eq_eq_false,
    decide_eq_true_eq, decide_eq_false_iff_not, not_not, List.mem_range,
    Nat.lt_succ_iff, LDFA.atCut, targetDFA_deadT]

/-- Enrichment can only postpone the first rejection. -/
theorem rawJ_le_J {u : List (Fin n)} {j : ℕ} (hj : (extractS c φ ψ p q).J u = some j) :
    ∃ r, extractRawJ c φ ψ p u = some r ∧ r ≤ j := by
  classical
  obtain ⟨hr, hjlen, _⟩ := ((extractS c φ ψ p q).J_eq_some_iff u j).mp hj
  have ht := ((extractS_rej_iff p q u j).mp hr).1
  cases hh : extractRawJ c φ ψ p u with
  | none =>
    have hn : ∀ i ≤ u.length, DeadT c φ p (u.take i) := by
      simpa [extractRawJ, List.find?_eq_none, LDFA.atCut, targetDFA_deadT,
        Nat.lt_succ_iff] using hh
    exact False.elim (ht (hn j hjlen))
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have hs := (extractRawJ_eq_some_iff p u r).mp hh
    by_contra hn
    exact ht (hs.2.2 j (by omega))

/-- Safety is exactly absence of positive-unit membership. -/
theorem extractS_safe (t : List (Fin n)) :
    (extractS c φ ψ p q).SafeFrom (extractS c φ ψ p q).A.start t ↔
      (q.1, q.2, t) ∉ Mu c φ := by
  rw [mu_membership]
  simp [SS2.SafeFrom, extractS, Bound.Q, LDFA.run, Finset.mem_range, Nat.lt_succ_iff]

/-- Proper head prefixes are enriched support, without semantic hypotheses. -/
theorem extractS_fh : (extractS c φ ψ p q).FH := by
  intro a b hab _ γ hγ i hi hr
  have hhead : (a ∩ b).Nonempty := by simpa [extractS] using hab
  have hp : (Bound.P (signedSys c ψ) (.inl p.1, p.2) γ).Nonempty := by
    change Bound.P (signedSys c ψ) (.inl p.1, p.2) γ = b at hγ
    rw [hγ]
    exact hhead.mono Finset.inter_subset_right
  exact ((extractS_rej_iff p q γ i).mp hr).2 (head_prefix_deadU hp hi)

/-- Nonempty antecedent upper cuts precede every enriched first rejection. -/
theorem extractS_cut_le_J {u : List (Fin n)} {i j : ℕ}
    (hj : (extractS c φ ψ p q).J u = some j) (hi : i ≤ u.length)
    (hp : (Bound.P (signedSys c φ) p (u.take i)).Nonempty) : i ≤ j := by
  have ht := ((extractS_rej_iff p q u j).mp
    (((extractS c φ ψ p q).J_eq_some_iff u j).mp hj).1).1
  by_contra hn
  have he := cone ht (by omega : j < i) hi
  simp [he] at hp

/-- Pointwise cross events. Defined enriched J is essential here. -/
theorem extractS_event_at_iff {t u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) (e i : ℕ) :
    (extractS c φ ψ p q).Event t u e i ↔
      i ≤ u.length ∧ e ≤ t.length ∧ (u.drop i).IsPrefix (t.drop e) ∧
      (Bound.P (signedSys c φ) p (u.take i) ∩
        Bound.Q (signedSys c φ) q (t.take e)).Nonempty := by
  constructor
  · rintro ⟨⟨he, hi, hpre⟩, _, hg⟩
    exact ⟨hi, he, hpre, (extractS_guard_iff p q t u e i).mp hg⟩
  · rintro ⟨hi, he, hpre, hg⟩
    refine ⟨⟨he, hi, hpre⟩, ?_, (extractS_guard_iff p q t u e i).mpr hg⟩
    cases hj : (extractS c φ ψ p q).J u with
    | none => simp [hj] at hJ
    | some j => exact ⟨j, rfl, extractS_cut_le_J p q hj hi
        (hg.mono Finset.inter_subset_left)⟩

/-- Extracted comparison events are exactly the cut-based antecedent events. -/
theorem extractS_event_iff {t u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) :
    (∃ e i, (extractS c φ ψ p q).Event t u e i) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Bound.P (signedSys c φ) p (u.take i) ∩
          Bound.Q (signedSys c φ) q (t.take e)).Nonempty := by
  simp only [extractS_event_at_iff p q hJ]
  constructor
  · rintro ⟨e, i, hi, he, hpre, hg⟩; exact ⟨i, hi, e, he, hpre, hg⟩
  · rintro ⟨i, hi, e, he, hpre, hg⟩; exact ⟨e, i, hi, he, hpre, hg⟩

/-- Pointwise self events, using the second upper cut for the cone bound. -/
theorem extractS_selfEvent_at_iff {u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) (i j : ℕ) :
    (extractS c φ ψ p q).SelfEvent u i j ↔ SelfEv c φ p u i j := by
  have hg := targetDFA_selfGuard (c := c) (φ := φ) (ψ := ψ) p u i j
  constructor
  · rintro ⟨hij, ⟨_, hj, hpre⟩, _, hguard⟩
    exact ⟨hij, hj, hpre, hg.mp hguard⟩
  · rintro ⟨hij, hj, hpre, hguard⟩
    refine ⟨hij, ⟨by omega, hj, hpre⟩, ?_, hg.mpr hguard⟩
    have hp := (flip_inter_symm.mp hguard).mono Finset.inter_subset_left
    cases hk : (extractS c φ ψ p q).J u with
    | none => simp [hk] at hJ
    | some k => exact ⟨k, rfl, extractS_cut_le_J p q hk hj hp⟩

/-- Extracted self events agree with antecedent self collisions. -/
theorem extractS_selfEvent_iff {u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) :
    (∃ i j, (extractS c φ ψ p q).SelfEvent u i j) ↔
      ∃ i j, SelfEv c φ p u i j := by
  simp only [extractS_selfEvent_at_iff p q hJ]

/-- A consequent path supplies an extracted head event. -/
theorem extractS_head (t u : List (Fin n)) :
    (extractS c φ ψ p q).HasHeadEvent t u ↔
      Moves c ψ (.inl p.1, p.2, u) (.inl q.1, q.2, t) := by
  change _ ↔ Relation.ReflTransGen (Move c ψ) _ _
  rw [lowest_point_leaf]
  simp only [SS2.HasHeadEvent, SS2.HeadEvent, SS2.Aligned, extractS,
    Bound.upper_atCut, Bound.lower_atCut, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_range, Nat.lt_succ_iff, Finset.inter_comm]
  constructor
  · rintro ⟨e, he, i, hi, ⟨_, _, h⟩, hg⟩
    exact ⟨i, hi, e, he, h.symm, hg⟩
  · rintro ⟨i, hi, e, he, h, hg⟩
    exact ⟨e, he, i, hi, ⟨he, hi, h.symm⟩, hg⟩

/-- Failure of antecedent closure excludes all extracted comparison events. -/
theorem extractS_no_events {t u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) :
    (∀ e ∈ Finset.range (t.length + 1), ∀ i ∈ Finset.range (u.length + 1),
      ¬ (extractS c φ ψ p q).Event t u e i) ↔
    ¬ ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
      (Bound.P (signedSys c φ) p (u.take i) ∩
        Bound.Q (signedSys c φ) q (t.take e)).Nonempty := by
  rw [← extractS_event_iff p q hJ]
  constructor
  · intro h ⟨e, i, he⟩
    exact h e (Finset.mem_range.mpr (by have := he.1.1; omega))
      i (Finset.mem_range.mpr (by have := he.1.2.1; omega)) he
  · intro h e _ i _ he; exact h ⟨e, i, he⟩

/-- Liveness excludes extracted self events. -/
theorem extractS_noSelf {u : List (Fin n)}
    (hJ : ((extractS c φ ψ p q).J u).isSome = true) :
    (extractS c φ ψ p q).NoSelf u ↔ ¬ ∃ i j, SelfEv c φ p u i j := by
  rw [SS2Self.noSelf_iff]
  simp only [extractS_selfEvent_at_iff p q hJ, not_exists]

/-- Holes are exactly the live pure-path failures of closure, under (U). -/
theorem extractS_isHoleS_iff (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ)
    (t u : List (Fin n)) :
    (extractS c φ ψ p q).IsHoleS t u ↔
      Live c φ (p.1, p.2, u) ∧
      Moves c ψ (.inl p.1, p.2, u) (.inl q.1, q.2, t) ∧
      (q.1, q.2, t) ∉ Cl c φ (p.1, p.2, u) := by
  classical
  have hlive := dead_iff_unit_or_self (sat_iff_mu.mp hφ) (p := p) (u := u)
  constructor
  · rintro ⟨⟨hs, hj, he, hh⟩, hn⟩
    have ht := ((extractS_J_isSome p q u).mp hj).1
    have hns := (extractS_noSelf p q hj).mp hn
    have hl : Live c φ (p.1, p.2, u) := by
      by_contra hn
      exact (hlive.mp hn).elim ht hns
    refine ⟨hl, (extractS_head p q t u).mp hh, ?_⟩
    rw [cl_membership_live hl]
    exact not_or.mpr ⟨(extractS_safe p q t).mp hs, (extractS_no_events p q hj).mp he⟩
  · rintro ⟨hl, hh, hc⟩
    have ht : ¬ DeadT c φ p u := fun h => deadT_not_live h hl
    have hu : ¬ DeadU c ψ p u := fun h => (condU_iff.mp hU) p.1 p.2 u h hl
    have hj := (extractS_J_isSome p q u).mpr ⟨ht, hu⟩
    have hcl := not_or.mp (mt (cl_membership_live hl).mpr hc)
    refine ⟨⟨(extractS_safe p q t).mpr hcl.1, hj,
      (extractS_no_events p q hj).mpr hcl.2, (extractS_head p q t u).mpr hh⟩,
      (extractS_noSelf p q hj).mpr ?_⟩
    intro hs
    exact (hlive.mpr (Or.inr hs)) hl

/-- The extracted interface for the finite decision procedure. -/
theorem condII_iff_no_holes (hφ : ∃ ρ, SatT c ρ φ) (hU : CondU c φ ψ) :
    CondII c φ ψ ↔ ∀ p q, ¬ (extractS c φ ψ p q).HasHoleS := by
  rw [condII_iff_moves]
  constructor
  · intro h p q ⟨t, u, hh⟩
    obtain ⟨hl, hm, hn⟩ := (extractS_isHoleS_iff p q hφ hU t u).mp hh
    exact hn (h (p.1, p.2, u) (q.1, q.2, t) hl hm)
  · intro h ⟨p, s, u⟩ ⟨q, s', t⟩ hl hm
    by_contra hn
    exact h (p, s) (q, s') ⟨t, u, (extractS_isHoleS_iff _ _ hφ hU t u).mpr ⟨hl, hm, hn⟩⟩

/-- Satisfiability-dispatched reduction, with (U) tested before holes. -/
theorem mixed_reduction (hφ : ∃ ρ, SatT c ρ φ) (hψ : ∃ ρ, SatT c ρ ψ) :
    ExistsEntailsT c φ ψ ↔ CondI0 c φ ψ ∧ CondU c φ ψ ∧
      ∀ p q, ¬ (extractS c φ ψ p q).HasHoleS := by
  rw [three_conditions_mixed hφ hψ]
  constructor
  · rintro ⟨hi, hu, hii⟩; exact ⟨hi, hu, (condII_iff_no_holes hφ hu).mp hii⟩
  · rintro ⟨hi, hu, hh⟩; exact ⟨hi, hu, (condII_iff_no_holes hφ hu).mpr hh⟩

namespace ExtractExamples
open DeciNSSE

/-- The binary arrow variance for the raw-cut counterexample. -/
def arrow : Fin 2 → Bool := ![true, false]

/-- Visible false = x, true = y; hidden false = a, true = c. -/
def antecedent : List (LitT 2 Bool) := [.lef false ![false, false]]
/-- The consequent used to distinguish raw and enriched rejection cuts. -/
def consequent : List (LitT 2 (Bool ⊕ Bool)) :=
  [.lef (.inl false) ![.inr false, .inl false],
   .fle ![.inr true, .inl true] (.inr false)]

/-- A visible assignment separating antecedent and consequent. -/
def countermodel (v : Bool) : Tree 2 :=
  if v then DeciNSSE.Tree.top else
    DeciNSSE.Tree.node ![DeciNSSE.Tree.node ![DeciNSSE.Tree.bot, DeciNSSE.Tree.bot],
      DeciNSSE.Tree.bot]

/-- The separating assignment satisfies the antecedent. -/
theorem countermodel_sat : SatT arrow countermodel antecedent := by
  simp only [SatT, antecedent, List.mem_singleton, forall_eq, HoldsT, countermodel,
    Bool.false_eq_true, ↓reduceIte]
  apply (node_treeLe_node_iff _ _ _).mpr
  intro i
  fin_cases i <;> simp [countermodel, arrow, node_treeLe_node_iff, treeLe_refl]

/-- The counterexample antecedent is satisfiable. -/
theorem antecedent_sat : ∃ ρ, SatT arrow ρ antecedent := ⟨countermodel, countermodel_sat⟩

/-- The counterexample consequent is satisfiable. -/
theorem consequent_sat : ∃ ρ, SatT arrow ρ consequent := by
  refine ⟨Sum.elim (fun _ => DeciNSSE.Tree.bot) (fun _ => DeciNSSE.Tree.top), ?_⟩
  simp [SatT, HoldsT, consequent]

/-- For negative-unit avoidance only, consistency of this larger set is unnecessary. -/
def unitEnvelope (S : Set (Config 2 Bool)) : Set (Config 2 (Bool ⊕ Bool)) :=
  {a | match a.1, a.2.1 with
    | .inl false, false => (false, false, a.2.2) ∈ S
    | .inr false, true => (false, false, 0 :: a.2.2) ∈ S
    | _, _ => True}

/-- The unit envelope is clause closed. -/
theorem unitEnvelope_closed {S : Set (Config 2 Bool)} (hS : Sol arrow antecedent S) :
    Closed arrow consequent (unitEnvelope S) := by
  intro p q h hp
  cases h with
  | extend v s w i =>
    cases v with
    | inl v => cases v <;> cases s <;> simp only [unitEnvelope, Set.mem_ofPred_eq] at hp ⊢
               exact hS.closed (.extend _ _ _ _) hp
    | inr v => cases v <;> cases s <;> simp only [unitEnvelope, Set.mem_ofPred_eq] at hp ⊢
               exact hS.closed (.extend _ _ _ _) hp
  | move hm =>
    cases hm with
    | copyPlus hl => simp [consequent] at hl
    | copyMinus hl => simp [consequent] at hl
    | flePush i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
        reduceCtorEq, false_or, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i <;> trivial
    | flePop i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
        reduceCtorEq, false_or, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i <;> trivial
    | lefPush i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
        reduceCtorEq, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      trivial
    | lefPop i hl =>
      simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
        reduceCtorEq, or_false] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i
      · exact hp
      · exact hS.closed (.move (.lefPop (a := ![false, false]) 1 (by simp [antecedent]))) hp

/-- The unit envelope avoids negative roots. -/
theorem unitEnvelope_avoids {S : Set (Config 2 Bool)} (hS : Sol arrow antecedent S) :
    Avoids consequent (unitEnvelope S) := by
  intro n hn hneg
  cases hneg with
  | lef hl =>
    simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.lef.injEq,
      reduceCtorEq, or_false] at hl
    rcases hl with ⟨rfl, rfl⟩
    exact hS.avoids hn (.lef (a := ![false, false]) (by simp [antecedent]))
  | fle hl =>
    simp only [consequent, List.mem_cons, List.not_mem_nil, LitT.fle.injEq,
      reduceCtorEq, false_or, or_false] at hl
    rcases hl with ⟨rfl, rfl⟩
    have hm : (false, true, []) ∈ S :=
      hS.closed (.move (.lefPop (a := ![false, false]) 0 (by simp [antecedent]))) hn
    exact hS.consistent (.pair false [0]) hn (hS.closed (.extend _ _ _ 0) hm)

/-- The unit premise holds for the whole system, not merely the exhibited seed. -/
theorem condU : CondU arrow antecedent consequent := by
  rintro ⟨x, s, w⟩ ⟨S, hS, ha⟩ n hn hr
  have hseed : visible (Z := Bool) (x, s, w) ∈ unitEnvelope S := by
    cases x <;> cases s <;> simp_all [visible, unitEnvelope]
  exact unitEnvelope_avoids hS (hr.mem_of_closed (unitEnvelope_closed hS) hseed) hn

/-- The counterexample source atom is live. -/
theorem source_live : Live arrow antecedent (false, false, [0, 1]) := by
  refine ⟨configSet arrow countermodel, (sat_iff_sol _).mp countermodel_sat, ?_⟩
  simp [configSet, countermodel, arrow]

/-- The target atom is outside the source's antecedent closure. -/
theorem target_not_cl :
    (true, true, []) ∉ Cl arrow antecedent (false, false, [0, 1]) := by
  intro h
  have hm := cl_subset ((sat_iff_sol _).mp countermodel_sat)
    (show (false, false, [0, 1]) ∈ configSet arrow countermodel by
      simp [configSet, countermodel, arrow]) h
  simp [configSet, countermodel] at hm

/-- The consequent provides the required head path. -/
theorem head_moves :
    Moves arrow consequent (.inl false, false, [0, 1]) (.inl true, true, []) := by
  apply Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Move.lefPop (c := arrow) (χ := consequent)
      (a := ![.inr false, .inl false]) 0 (by simp [consequent])))
  exact Relation.ReflTransGen.single (Move.flePop (c := arrow) (χ := consequent)
    (a := ![.inr true, .inl true]) 1 (by simp [consequent]))

/-- The hole is witnessed by liveness and a concrete tree model, without powerset-state
enumeration. -/
theorem hole :
    (extractS arrow antecedent consequent (false, false) (true, true)).IsHoleS [] [0, 1] :=
  (extractS_isHoleS_iff _ _ antecedent_sat condU _ _).mpr
    ⟨source_live, head_moves, target_not_cl⟩

/-- The head upper summary is nonempty. -/
theorem head_upper_nonempty :
    (Bound.P (signedSys arrow consequent) (.inl false, false) [0, 1]).Nonempty := by
  exact ⟨(.inl true, true), (mem_P_iff_moves _).mpr (moves_iff_signed.mp head_moves)⟩

/-- All proper head prefixes, including the raw rejected cut, are in DeadU. -/
theorem head_prefix_supported (i : ℕ) (hi : i < 2) :
    DeadU arrow consequent (false, false) ([0, 1].take i) :=
  head_prefix_deadU head_upper_nonempty hi

/-- The raw reader supports the empty prefix. -/
theorem raw_root_supported : DeadT arrow antecedent (false, false) [] := by
  apply Or.inl
  apply reach_neg_iff.mp
  exact ⟨(false, false, []), .lef (a := ![false, false]) (by simp [antecedent]), .refl⟩

/-- The counterexample antecedent has no positive units. -/
theorem no_facts {a : Config 2 Bool} : ¬ Fact antecedent a := by
  intro h
  cases h <;> simp_all [antecedent]

/-- A closed, negative-unit-avoiding set containing x⁺(0), although inconsistent. -/
def rawEnvelope : Set (Config 2 Bool) :=
  {a | a.2.1 = true ∨ ∃ w, a.2.2 = 0 :: w}

/-- The raw envelope is clause closed. -/
theorem rawEnvelope_closed : Closed arrow antecedent rawEnvelope := by
  intro p q h hp
  cases h with
  | extend v s w i =>
    rcases hp with hs | ⟨v, rfl⟩
    · exact Or.inl hs
    · exact Or.inr ⟨v ++ [i], rfl⟩
  | move hm =>
    cases hm with
    | copyPlus hl => simp [antecedent] at hl
    | copyMinus hl => simp [antecedent] at hl
    | flePush i hl => simp [antecedent] at hl
    | flePop i hl => simp [antecedent] at hl
    | lefPush i hl => exact Or.inl rfl
    | lefPop i hl =>
      simp only [antecedent, List.mem_singleton, LitT.lef.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · simp [rawEnvelope] at hp

/-- The raw envelope avoids forbidden root atoms. -/
theorem rawEnvelope_avoids : Avoids antecedent rawEnvelope := by
  intro n hn hneg
  cases hneg with
  | fle hl => simp [antecedent] at hl
  | lef hl =>
    simp only [antecedent, List.mem_singleton, LitT.lef.injEq] at hl
    rcases hl with ⟨rfl, rfl⟩
    simp [rawEnvelope] at hn

/-- The one-letter prefix is unsupported in the raw reader. -/
theorem raw_one_unsupported : ¬ DeadT arrow antecedent (false, false) [0] := by
  rintro (hn | ⟨δ, hm⟩)
  · obtain ⟨n, hn, hr⟩ := reach_neg_iff.mpr hn
    exact rawEnvelope_avoids
      (hr.mem_of_closed rawEnvelope_closed (Or.inr ⟨[], rfl⟩)) hn
  · obtain ⟨a, ha, _⟩ := mem_mu.mp hm
    exact no_facts ha

/-- The raw first-rejection cut is one. -/
theorem rawJ_one : extractRawJ arrow antecedent consequent (false, false) [0, 1] = some 1 := by
  apply (extractRawJ_eq_some_iff _ _ _).mpr
  refine ⟨raw_one_unsupported, by decide, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  exact raw_root_supported

/-- The enriched first-rejection cut is two. -/
theorem enrichedJ_two :
    (extractS arrow antecedent consequent (false, false) (true, true)).J [0, 1] = some 2 := by
  apply (SS2.J_eq_some_iff _ _ _).mpr
  refine ⟨?_, by decide, ?_⟩
  · apply (extractS_rej_iff _ _ _ _).mpr
    exact ⟨fun h => deadT_not_live h source_live,
      fun h => condU_iff.mp condU false false _ h source_live⟩
  · intro i hi hr
    exact ((extractS_rej_iff _ _ _ _).mp hr).2 (head_prefix_supported i hi)

/-- The head is after the raw cut and exactly at the enriched cut. -/
theorem head_at_two :
    (extractS arrow antecedent consequent (false, false) (true, true)).HeadEvent
      [] [0, 1] 0 2 := by
  obtain ⟨e, he, i, hi, hh⟩ :=
    (extractS_head (false, false) (true, true) [] [0, 1]).mpr head_moves
  have he0 : e = 0 := by simp at he; omega
  subst e
  have hi2 : i = 2 := by
    have hd := congrArg List.length hh.1.2.2
    simp only [List.drop_nil, List.length_nil, List.length_drop, List.length_cons] at hd
    simp at hi
    omega
  subst i
  exact hh

/-- The defined-cut hypothesis really is necessary, even under (U): the raw unit-unsupported
prefix has a reflexive overlap, but enriched J is undefined. -/
theorem event_premise_needed :
    ¬ DeadT arrow antecedent (false, false) [0] ∧
    (Bound.P (signedSys arrow antecedent) (false, false) [] ∩
      Bound.Q (signedSys arrow antecedent) (false, false) []).Nonempty ∧
    ¬ ∃ e i, (extractS arrow antecedent consequent (false, false) (false, false)).Event
      [0] [0] e i := by
  refine ⟨raw_one_unsupported, ?_, ?_⟩
  · refine ⟨(false, false), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;>
      simp only [Bound.P_nil, Bound.Q_nil, Bound.mem_up, Bound.mem_down] <;>
      exact Bound.d_refl _ _
  · rintro ⟨e, i, _, ⟨j, hj, _⟩, _⟩
    have hsome :
        ((extractS arrow antecedent consequent (false, false) (false, false)).J [0]).isSome =
          true := by
      rw [show (extractS arrow antecedent consequent (false, false) (false, false)).J [0] =
        some j from hj]
      rfl
    have hdead : DeadU arrow consequent (false, false) [0] := head_prefix_supported 1 (by decide)
    exact ((extractS_J_isSome _ _ _).mp hsome).2 hdead

/-- The example also inhabits (I0), so its failed test is precisely (II). -/
theorem condI0 : CondI0 arrow antecedent consequent := by
  intro b hb
  obtain ⟨a, ha, _⟩ := mem_mu.mp hb
  cases ha <;> simp_all [consequent]

/-- The counterexample violates the singleton closure condition. -/
theorem not_condII : ¬ CondII arrow antecedent consequent := by
  intro h
  exact (condII_iff_no_holes antecedent_sat condU).mp h
    (false, false) (true, true) ⟨[], [0, 1], hole⟩

/-- The counterexample fails existential entailment. -/
theorem not_entails : ¬ ExistsEntailsT arrow antecedent consequent := by
  intro h
  exact not_condII (condII_of_existsEntailsT h)

/-- A third-child witness for the semantic hole equivalence and its premises. -/
def ternaryConsequent : List (LitT 3 (Bool ⊕ Unit)) :=
  [.le (.inl false) (.inl true)]

/-- The ternary example satisfies the unit condition. -/
theorem ternary_condU : CondU LeafHornExamples.arrow [] ternaryConsequent := by
  intro a ha b hb
  cases hb <;> simp_all [ternaryConsequent]

/-- Both systems in the ternary example are satisfiable. -/
theorem ternary_satisfiable :
    (∃ ρ : Bool → Tree 3, SatT LeafHornExamples.arrow ρ []) ∧
    (∃ ρ, SatT LeafHornExamples.arrow ρ ternaryConsequent) := by
  constructor
  · exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT]⟩
  · exact ⟨fun _ => DeciNSSE.Tree.bot, by simp [SatT, HoldsT, ternaryConsequent, treeLe_refl]⟩

/-- The ternary extracted instance has a concrete hole. -/
theorem ternary_hole :
    (extractS LeafHornExamples.arrow [] ternaryConsequent
      (false, false) (true, false)).IsHoleS [2] [2] := by
  let ρ : Bool → Tree 3 := fun v => if v then DeciNSSE.Tree.bot else DeciNSSE.Tree.top
  have hs : Sol LeafHornExamples.arrow [] (configSet LeafHornExamples.arrow ρ) :=
    (sat_iff_sol _).mp (by simp [SatT])
  have hp : (false, false, [2]) ∈ configSet LeafHornExamples.arrow ρ := by
    simp [configSet, ρ]
  apply (extractS_isHoleS_iff _ _ ternary_satisfiable.1 ternary_condU _ _).mpr
  refine ⟨⟨_, hs, hp⟩, Relation.ReflTransGen.single (.copyPlus (by simp [ternaryConsequent])), ?_⟩
  intro h
  have hq := cl_subset hs hp h
  simp [configSet, ρ] at hq

/-- The ternary extraction has unconditional FH and an actual hole. -/
theorem ternary_hypotheses :
    (extractS LeafHornExamples.arrow [] ternaryConsequent (false, false) (true, false)).FH ∧
    (extractS LeafHornExamples.arrow [] ternaryConsequent (false, false) (true, false)).HasHoleS :=
  ⟨extractS_fh _ _, [2], [2], ternary_hole⟩

/-- The empty alphabet still has a defined first rejection, at its only cut. -/
theorem nullary_J :
    (extractS (n := 0) (fun _ => false) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))) ((), false) ((), false)).J [] = some 0 := by
  apply (SS2.J_eq_some_iff _ _ _).mpr
  exact ⟨MembershipExamples.nullary_reader_rej, by decide, by omega⟩

/-- FH also specializes at arity zero without an inhabitant of the alphabet. -/
theorem nullary_fh :
    (extractS (n := 0) (fun _ => false) ([] : List (LitT 0 Unit))
      ([] : List (LitT 0 (Unit ⊕ Unit))) ((), false) ((), false)).FH :=
  extractS_fh _ _

end ExtractExamples

end DeciENSSE.Core.Mixed
