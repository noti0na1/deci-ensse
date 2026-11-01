import DeciENSSE.Core.Mixed.Membership

/-! # Computable satisfiability of mixed systems

Finite state searches decide satisfiability of mixed literal systems
over arbitrary trees, including the empty alphabet.

## Main declarations

- `muDFA`, `muDFA_accept`, `avoids_mu_iff`,
  `muCollision_short`, `consistent_mu_iff`, `decideSatMixed`.
-/

namespace DeciENSSE.Core.Mixed

variable {n : ℕ}
open DeciENSSE.Core.Full

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

/-- Lower summary and a sticky flag recording any positive-fact hit. -/
abbrev MuState (V : Type*) := Finset (V × Bool) × Bool

/-- Track lower summaries and a sticky positive-unit hit. -/
def muDFA (p : V × Bool) : LDFA (Fin n) (MuState V) where
  start := (Bound.down (signedSys c χ) p,
    decide ((Bound.down (signedSys c χ) p ∩ PF c χ).Nonempty))
  step S b :=
    let Q := Bound.qstep (signedSys c χ) S.1 b
    (Q, S.2 || decide ((Q ∩ PF c χ).Nonempty))

private theorem prefixHit_snoc (H : List (Fin n) → Prop) (w : List (Fin n)) (b : Fin n) :
    (∃ e ≤ (w ++ [b]).length, H ((w ++ [b]).take e)) ↔
      (∃ e ≤ w.length, H (w.take e)) ∨ H (w ++ [b]) := by
  constructor
  · rintro ⟨e, he, hh⟩
    by_cases h : e ≤ w.length
    · exact Or.inl ⟨e, h, by simpa [List.take_append_of_le_length h] using hh⟩
    · have heq : e = (w ++ [b]).length := by simp at he ⊢; omega
      subst e
      exact Or.inr (by simpa only [List.take_length] using hh)
  · rintro (⟨e, he, hh⟩ | hh)
    · exact ⟨e, by simp; omega, by simpa [List.take_append_of_le_length he] using hh⟩
    · exact ⟨(w ++ [b]).length, le_rfl, by simpa only [List.take_length] using hh⟩

/-- The run records the lower summary and positive-unit prefix hits. -/
theorem muDFA_run (p : V × Bool) (w : List (Fin n)) :
    ((muDFA c χ p).run w).1 = Bound.Q (signedSys c χ) p w ∧
    (((muDFA c χ p).run w).2 = true ↔ ∃ e ≤ w.length,
      (Bound.Q (signedSys c χ) p (w.take e) ∩ PF c χ).Nonempty) := by
  induction w using List.reverseRecOn with
  | nil => simp [muDFA, LDFA.run, LDFA.runFrom]
  | append_singleton w b ih =>
    have hs : (muDFA c χ p).run (w ++ [b]) =
        (muDFA c χ p).step ((muDFA c χ p).run w) b := by
      simp [LDFA.run, LDFA.runFrom, List.foldl_append]
    rw [hs]
    change Bound.qstep (signedSys c χ) _ b = _ ∧
      ((_ || decide ((Bound.qstep (signedSys c χ) _ b ∩ PF c χ).Nonempty)) = true ↔ _)
    rw [ih.1, ← Bound.Q_snoc]
    refine ⟨rfl, ?_⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, ih.2]
    exact (prefixHit_snoc (fun t => (Bound.Q (signedSys c χ) p t ∩ PF c χ).Nonempty)
      w b).symm

/-- The hit includes cut zero and persists after the lower summary becomes empty. -/
theorem muDFA_accept (p : V × Bool) (w : List (Fin n)) :
    ((muDFA c χ p).run w).2 = true ↔ (p.1, p.2, w) ∈ Mu c χ :=
  (muDFA_run c χ p w).2.trans mu_membership.symm

/-- Negative units are roots, so avoidance is a finite down-summary test. -/
theorem avoids_mu_iff : Avoids χ (Mu c χ) ↔
    ∀ n ∈ negList χ,
      ¬ (Bound.down (signedSys c χ) (n.1, n.2.1) ∩ PF c χ).Nonempty := by
  constructor
  · intro h n hn hh
    have hn' := mem_negList.mp hn
    have hw := hn'.word_nil
    apply h (p := n) _ hn'
    rcases n with ⟨v, s, w⟩
    dsimp at hw; subst w
    exact mu_membership.mpr ⟨0, by simp, by simpa using hh⟩
  · intro h n hm hn
    have hw := hn.word_nil
    have hh := h n (mem_negList.mpr hn)
    rcases n with ⟨v, s, w⟩
    dsimp at hw; subst w
    apply hh
    simpa only [mu_membership, List.length_nil, Nat.le_zero, exists_eq_left,
      List.take_zero, Bound.Q_nil] using hm

/-- Decide whether unit closure avoids all forbidden root atoms. -/
def decideAvoidsMu : Decidable (Avoids χ (Mu c χ)) :=
  decidable_of_iff
    (∀ n ∈ negList χ,
      ¬ (Bound.down (signedSys c χ) (n.1, n.2.1) ∩ PF c χ).Nonempty)
    (avoids_mu_iff c χ).symm

/-- The two signs must hit along the same word, possibly at different cuts. -/
def MuCollision (v : V) (w : List (Fin n)) : Prop :=
  ((muDFA c χ (v, false)).run w).2 = true ∧
    ((muDFA c χ (v, true)).run w).2 = true

/-- The finite predicate has a computable decision. -/
instance (v : V) (w : List (Fin n)) : Decidable (MuCollision c χ v w) := by
  unfold MuCollision; infer_instance

/-- A unit collision is simultaneous acceptance in the two signed readers. -/
theorem muCollision_iff (v : V) (w : List (Fin n)) :
    MuCollision c χ v w ↔ (v, false, w) ∈ Mu c χ ∧ (v, true, w) ∈ Mu c χ := by
  simp only [MuCollision, muDFA_accept]

/-- Uniform state count for the product of the two signed membership readers. -/
def muCollisionBound (V : Type*) [Fintype V] : ℕ :=
  Fintype.card (MuState V × MuState V)

/-- A collision has a witness bounded by the product-state count. -/
theorem muCollision_short {v : V} {w : List (Fin n)} (h : MuCollision c χ v w) :
    ∃ u, u.length < muCollisionBound V ∧ MuCollision c χ v u := by
  let M := (muDFA c χ (v, false)).prod (muDFA c χ (v, true))
  obtain ⟨u, hu, _, he⟩ := M.short_safe_path (fun _ => True) M.start w
    ((M.pathSafe_iff _ _ _).mpr (by simp))
  change M.run u = M.run w at he
  have hh : (M.run w).1.2 = true ∧ (M.run w).2.2 = true := by
    simpa only [M, LDFA.prod_run, MuCollision] using h
  refine ⟨u, hu, ?_⟩
  rw [← he] at hh
  simpa only [M, LDFA.prod_run, MuCollision] using hh

/-- Consistency of unit closure is absence of bounded collisions. -/
theorem consistent_mu_iff : Consistent (Mu c χ) ↔
    ∀ v, ∀ w ∈ wordsUpTo (muCollisionBound V), ¬ MuCollision c χ v w := by
  constructor
  · intro h v w _ hh
    obtain ⟨hp, hm⟩ := (muCollision_iff c χ v w).mp hh
    exact h (.pair v w) hp hm
  · intro h p q he hp hm
    cases he with
    | pair v w =>
      obtain ⟨u, hu, hh⟩ := muCollision_short c χ
        ((muCollision_iff c χ v w).mpr ⟨hp, hm⟩)
      exact h v u ((mem_wordsUpTo _ _).mpr (Nat.le_of_lt hu)) hh

/-- Decide consistency by finite collision search. -/
def decideConsistentMu : Decidable (Consistent (Mu c χ)) :=
  decidable_of_iff
    (∀ v, ∀ w ∈ wordsUpTo (muCollisionBound V), ¬ MuCollision c χ v w)
    (consistent_mu_iff c χ).symm

/-- Executable satisfiability, for every variance and finite variable type. -/
def decideSatMixed : Decidable (∃ ρ, SatT c ρ χ) := by
  letI := decideAvoidsMu c χ
  letI := decideConsistentMu c χ
  exact decidable_of_iff (Avoids χ (Mu c χ) ∧ Consistent (Mu c χ)) sat_iff_mu.symm

/-- The satisfiability decision returns true exactly on satisfiable systems. -/
theorem decideSatMixed_true_iff :
    @decide (∃ ρ, SatT c ρ χ) (decideSatMixed c χ) = true ↔ ∃ ρ, SatT c ρ χ :=
  @decide_eq_true_iff _ (decideSatMixed c χ)

namespace SatMixedExamples
open LeafHornExamples

/-- A satisfiable system that has no joint parity assignment. -/
theorem mixed_positive :
    @decide (∃ ρ, SatT arrow ρ mixed) (decideSatMixed arrow mixed) = true :=
  (decideSatMixed_true_iff _ _).mpr DualityExamples.mixed_sat

/-- A positive root unit forbidden by an upper constructor bound. -/
def rootClash : List (LitT n Unit) := [.top (), .lef () (fun _ => ())]

/-- The negative-root test has an actual obstruction, independent of consistency. -/
theorem root_not_avoids (c : Fin n → Bool) : ¬ Avoids rootClash (Mu c rootClash) := by
  intro h
  exact h (mem_mu.mpr ⟨((), false, []), .top (by simp [rootClash]), .refl⟩)
    (.lef (a := fun _ => ()) (by simp [rootClash]))

/-- Kernel evaluation of the actual root-rejection branch of the decider. -/
theorem root_negative :
    @decide (∃ ρ, SatT arrow ρ rootClash) (decideSatMixed arrow rootClash) = false := by
  decide +kernel

/-- Both extreme units on one variable. -/
def signClash : List (LitT n Unit) := [.top (), .bot ()]

/-- No negative units occur here; intrinsic disjointness detects the contradiction. -/
theorem sign_collision (c : Fin n → Bool) : MuCollision c signClash () [] := by
  apply (muCollision_iff _ _ _ _).mpr
  exact ⟨mem_mu.mpr ⟨((), false, []), .top (by simp [signClash]), .refl⟩,
    mem_mu.mpr ⟨((), true, []), .bot (by simp [signClash]), .refl⟩⟩

/-- Opposite extreme units introduce no negative root literals. -/
theorem sign_avoids (c : Fin n → Bool) : Avoids signClash (Mu c signClash) := by
  intro p _ hn
  cases hn <;> simp_all [signClash]

/-- The satisfiability decision rejects opposite extreme units. -/
theorem sign_negative (c : Fin n → Bool) :
    @decide (∃ ρ, SatT c ρ signClash) (decideSatMixed c signClash) = false := by
  rw [decide_eq_false_iff_not]
  intro hs
  obtain ⟨hp, hm⟩ := (muCollision_iff _ _ _ _).mp (sign_collision c)
  exact (sat_iff_mu.mp hs).2 (.pair () []) hp hm

/-- The lower summary is already empty after one edge, but the earlier hit remains. -/
theorem sticky_after_empty :
    (Bound.Q (signedSys arrow ([.top ()] : List (LitT 3 Unit))) ((), false) [2] = ∅) ∧
    ((muDFA arrow ([.top ()] : List (LitT 3 Unit)) ((), false)).run [2]).2 = true := by
  decide +kernel

/-- The executable procedure also covers the empty variable type. -/
theorem empty_variables :
    @decide (∃ ρ, SatT arrow ρ ([] : List (LitT 3 Empty)))
      (decideSatMixed arrow []) = true := by
  decide +kernel

/-- The root-rejection branch is executable even with no child letters. -/
theorem nullary_root_negative :
    @decide (∃ ρ, SatT (fun i : Fin 0 => i.elim0) ρ rootClash)
      (decideSatMixed (fun i : Fin 0 => i.elim0) rootClash) = false := by
  decide +kernel

end SatMixedExamples

end DeciENSSE.Core.Mixed
