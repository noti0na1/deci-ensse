import DeciENSSE.Core.Mixed.Duality
import DeciENSSE.Core.Mixed.Signed
import DeciENSSE.Core.Mixed.Conditions
import DeciENSSE.Core.Words.LDFA

/-! # Leaf closure membership, deadness, and the shared target reader

Finite automata recognize atoms forced by positive units and atoms whose
closure reaches a negative unit. The shared target reader also records self
events: two descendants of the same seed reach incompatible opposite signs.
These events detect dead seeds even when no negative unit is reachable.

## Main declarations

- `PF`, `mu_membership`, `NegDown`, `reach_neg_iff`,
  `DeadT`, `deadT_iff_state`, `SelfEv`, `dead_iff_unit_or_self`, `cone`,
  `cl_membership_live`, `DeadU`, `head_prefix_deadU`, `targetDFA`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words
open DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*}

/-- Enumerate positive root units as signed variables. -/
def factList (χ : List (LitT n V)) : List (Config n V) :=
  χ.flatMap fun l => match l with
    | .bot v => [(v, true, [])]
    | .top v => [(v, false, [])]
    | _ => []

/-- Enumerate forbidden root units as signed variables. -/
def negList (χ : List (LitT n V)) : List (Config n V) :=
  χ.flatMap fun l => match l with
    | .fle _ v => [(v, true, [])]
    | .lef v _ => [(v, false, [])]
    | _ => []

/-- The finite enumeration characterizes positive units. -/
@[simp] theorem mem_factList {χ : List (LitT n V)} {f : Config n V} :
    f ∈ factList χ ↔ Fact χ f := by
  constructor
  · intro h
    obtain ⟨l, hl, hf⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hf
    · subst f; exact .bot hl
    · subst f; exact .top hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

/-- The finite enumeration characterizes negative units. -/
@[simp] theorem mem_negList {χ : List (LitT n V)} {n : Config n V} :
    n ∈ negList χ ↔ Neg χ n := by
  constructor
  · intro h
    obtain ⟨l, hl, hn⟩ := List.mem_flatMap.mp h
    cases l <;> simp only [List.mem_singleton, List.not_mem_nil] at hn
    · subst n; exact .fle hl
    · subst n; exact .lef hl
  · intro h; cases h <;> apply List.mem_flatMap.mpr
    · exact ⟨_, ‹_›, by simp⟩
    · exact ⟨_, ‹_›, by simp⟩

/-- Every positive unit is at the empty word. -/
theorem Fact.word_nil {χ : List (LitT n V)} {f : Config n V} (h : Fact χ f) :
    f.2.2 = [] := by cases h <;> rfl

/-- Every negative unit is at the empty word. -/
theorem Neg.word_nil {χ : List (LitT n V)} {n : Config n V} (h : Neg χ n) :
    n.2.2 = [] := by cases h <;> rfl

/-- Endpoint-preserving bounded reachability; no decidability of the target is needed. -/
theorem bounded_run_iff {S : Type*} [Fintype S] (M : LDFA (Fin n) S)
    (q : S) (H : S → Prop) :
    (∃ w ∈ wordsUpTo (α := Fin n) (Fintype.card S), H (M.runFrom q w)) ↔
      ∃ w, H (M.runFrom q w) := by
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, _, he⟩ := M.short_safe_path (fun _ => True) q w
      ((M.pathSafe_iff _ _ _).mpr (by simp))
    exact ⟨v, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hv), he ▸ hw⟩

variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (χ : List (LitT n V))

/-- The finite lower summaries reachable from positive units. -/
def PF : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ f ∈ factList χ, ∃ β ∈ wordsUpTo (α := Fin n) (Fintype.card (Finset (V × Bool))),
    x ∈ Automata.P (signedSys c χ) (f.1, f.2.1) β

/-- The finite summaries leading to negative units. -/
def NegDown : Finset (V × Bool) := Finset.univ.filter fun x =>
  ∃ n ∈ negList χ, (x, (n.1, n.2.1)) ∈ Automata.D (signedSys c χ)

variable {c χ}

/-- Membership in the positive-unit summary has a unit witness. -/
theorem mem_PF {x : V × Bool} : x ∈ PF c χ ↔
    ∃ f β, Fact χ f ∧ x ∈ Automata.P (signedSys c χ) (f.1, f.2.1) β := by
  simp only [PF, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, β, _, hβ⟩; exact ⟨f, β, mem_factList.mp hf, hβ⟩
  · rintro ⟨f, β, hf, hβ⟩
    refine ⟨f, mem_factList.mpr hf, ?_⟩
    exact (bounded_run_iff (Automata.upper (signedSys c χ) (f.1, f.2.1))
      _ (fun S => x ∈ S)).mpr ⟨β, hβ⟩

/-- Membership in the negative-unit summary has a forbidden-unit witness. -/
theorem mem_NegDown {x : V × Bool} : x ∈ NegDown c χ ↔
    ∃ n, Neg χ n ∧ (x, (n.1, n.2.1)) ∈ Automata.D (signedSys c χ) := by
  simp [NegDown]

/-- Lower summaries characterize membership in unit closure. -/
theorem mu_membership {q : V} {s : Bool} {t : List (Fin n)} :
    (q, s, t) ∈ Mu c χ ↔ ∃ e ≤ t.length,
      (Automata.Q (signedSys c χ) (q, s) (t.take e) ∩ PF c χ).Nonempty := by
  constructor
  · rintro hm
    obtain ⟨⟨f, s', w⟩, hf, hr⟩ := mem_mu.mp hm
    have hw := hf.word_nil; dsimp at hw; subst w
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, _, e, he, _, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    exact ⟨e, he, r, Finset.mem_inter.mpr ⟨hq,
      mem_PF.mpr ⟨(f, s', []), α.take i, hf, hp⟩⟩⟩
  · rintro ⟨e, he, r, hr⟩
    obtain ⟨hq, hf⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨f, s', w⟩, β, hf, hp⟩ := mem_PF.mp hf
    have hw := hf.word_nil; dsimp at hw; subst w
    apply mem_mu.mpr
    refine ⟨(f, s', []), hf, reach_iff_moves.mpr ⟨β ++ t.drop e, ?_⟩⟩
    apply lowest_point_leaf.mpr
    refine ⟨β.length, by simp, e, he, by simp, r, ?_⟩
    simpa using Finset.mem_inter.mpr ⟨hp, hq⟩

/-- Upper summaries characterize reachability to a negative unit. -/
theorem reach_neg_iff {p : V} {s : Bool} {u : List (Fin n)} :
    (∃ n, Neg χ n ∧ Reach c χ (p, s, u) n) ↔
      ∃ z, (Automata.P (signedSys c χ) (p, s) (u ++ z) ∩ NegDown c χ).Nonempty := by
  constructor
  · rintro ⟨⟨n, sn, w⟩, hn, hr⟩
    have hw := hn.word_nil; dsimp at hw; subst w
    obtain ⟨z, hz⟩ := reach_iff_moves.mp hr
    have hp := (mem_P_iff_moves (u ++ z)).mpr (moves_iff_signed.mp hz)
    exact ⟨z, (n, sn), Finset.mem_inter.mpr ⟨hp,
      mem_NegDown.mpr ⟨(n, sn, []), hn, Automata.d_refl _ _⟩⟩⟩
  · rintro ⟨z, r, hr⟩
    obtain ⟨hp, hn⟩ := Finset.mem_inter.mp hr
    obtain ⟨⟨n, sn, w⟩, hn, hd⟩ := mem_NegDown.mp hn
    have hw := hn.word_nil; dsimp at hw; subst w
    refine ⟨(n, sn, []), hn, reach_iff_moves.mpr ⟨z, ?_⟩⟩
    apply moves_iff_signed.mpr
    exact ((mem_P_iff_moves _).mp hp).trans (Automata.d_moves hd [])

variable (c χ)

/-- Upper transition function with an arbitrary initial state. -/
def upperRun (S : Finset (V × Bool)) (w : List (Fin n)) : Finset (V × Bool) :=
  w.foldl (Automata.pstep (signedSys c χ)) S

/-- Some run of the upper automaton from the summary `S` meets `NegDown`, the variables below
a forbidden root; the runs are searched up to the number of summaries (`negReachS_iff`). -/
def negReachS (S : Finset (V × Bool)) : Prop :=
  ∃ z ∈ wordsUpTo (α := Fin n) (Fintype.card (Finset (V × Bool))),
    (upperRun c χ S z ∩ NegDown c χ).Nonempty

/-- The flipped summary meets `PF`: some signed variable of `S` has its opposite in the
summaries reachable from positive units. -/
def flipHitS (S : Finset (V × Bool)) : Prop :=
  (S.map flipEmb ∩ PF c χ).Nonempty

/-- Some run of the upper automaton from the summary `S` reaches a summary whose flip meets
`PF`; the runs are searched up to the number of summaries (`muReachS_iff`). -/
def muReachS (S : Finset (V × Bool)) : Prop :=
  ∃ z ∈ wordsUpTo (α := Fin n) (Fintype.card (Finset (V × Bool))),
    flipHitS c χ (upperRun c χ S z)

/-- `negReachS` is decidable by its bounded search. -/
instance (S : Finset (V × Bool)) : Decidable (negReachS c χ S) := by
  unfold negReachS; infer_instance
/-- `flipHitS` is decidable. -/
instance (S : Finset (V × Bool)) : Decidable (flipHitS c χ S) := by
  unfold flipHitS; infer_instance
/-- `muReachS` is decidable by its bounded search. -/
instance (S : Finset (V × Bool)) : Decidable (muReachS c χ S) := by
  unfold muReachS; infer_instance

/-- The negative-unit summary test has a path witness. -/
theorem negReachS_iff (S : Finset (V × Bool)) :
    negReachS c χ S ↔ ∃ z, (upperRun c χ S z ∩ NegDown c χ).Nonempty :=
  bounded_run_iff ⟨S, Automata.pstep (signedSys c χ)⟩ S
    (fun T => (T ∩ NegDown c χ).Nonempty)

/-- The positive-unit summary test has a path witness. -/
theorem muReachS_iff (S : Finset (V × Bool)) :
    muReachS c χ S ↔ ∃ z, flipHitS c χ (upperRun c χ S z) :=
  bounded_run_iff ⟨S, Automata.pstep (signedSys c χ)⟩ S _

/-- Running the upper automaton produces the upper summary. -/
@[simp] theorem upperRun_P (p : V × Bool) (u z : List (Fin n)) :
    upperRun c χ (Automata.P (signedSys c χ) p u) z =
      Automata.P (signedSys c χ) p (u ++ z) := (List.foldl_append).symm

/-- A seed is blocked by units or a same-prefix sign collision. -/
def DeadT (p : V × Bool) (u : List (Fin n)) : Prop :=
  (∃ z, (Automata.P (signedSys c χ) p (u ++ z) ∩ NegDown c χ).Nonempty) ∨
    ∃ δ, (p.1, !p.2, u ++ δ) ∈ Mu c χ

/-- A strict prefix-comparison event witnesses a self collision. -/
def SelfEv (p : V × Bool) (u : List (Fin n)) (i j : ℕ) : Prop :=
  i < j ∧ j ≤ u.length ∧ (u.drop j).IsPrefix (u.drop i) ∧
    (Automata.P (signedSys c χ) p (u.take i) ∩
      (Automata.P (signedSys c χ) p (u.take j)).map flipEmb).Nonempty

variable {c χ}

/-- A forced opposite atom is detected by the positive-unit summary. -/
theorem mu_flip_membership {p : V × Bool} {t : List (Fin n)} :
    (p.1, !p.2, t) ∈ Mu c χ ↔
      ∃ e ≤ t.length, flipHitS c χ (Automata.P (signedSys c χ) p (t.take e)) := by
  rw [mu_membership]
  change (∃ e ≤ t.length,
    (Automata.Q (signedSys c χ) (flipV p) (t.take e) ∩ PF c χ).Nonempty) ↔ _
  simp only [Q_flip, flipHitS]

/-- Unit deadness descends to prefixes. -/
theorem deadT_prefix {p : V × Bool} {u v : List (Fin n)} :
    DeadT c χ p (u ++ v) → DeadT c χ p u := by
  rintro (⟨z, hz⟩ | ⟨δ, hδ⟩)
  · exact Or.inl ⟨v ++ z, by simpa [List.append_assoc] using hz⟩
  · exact Or.inr ⟨v ++ δ, by simpa [List.append_assoc] using hδ⟩

/-- Unit deadness is a finite-state test with a past-hit flag. -/
theorem deadT_iff_state {p : V × Bool} {u : List (Fin n)} :
    DeadT c χ p u ↔
      negReachS c χ (Automata.P (signedSys c χ) p u) ∨
      muReachS c χ (Automata.P (signedSys c χ) p u) ∨
      ∃ e ≤ u.length, flipHitS c χ (Automata.P (signedSys c χ) p (u.take e)) := by
  rw [negReachS_iff, muReachS_iff]
  simp only [upperRun_P]
  constructor
  · rintro (hn | ⟨δ, hδ⟩)
    · exact Or.inl hn
    obtain ⟨e, he, hh⟩ := mu_flip_membership.mp hδ
    by_cases h : e ≤ u.length
    · exact Or.inr (Or.inr ⟨e, h, by simpa [List.take_append_of_le_length h] using hh⟩)
    · exact Or.inr (Or.inl ⟨δ.take (e - u.length), by
        simpa [List.take_append, List.take_of_length_le (by omega : u.length ≤ e)] using hh⟩)
  · rintro (hn | ⟨z, hz⟩ | ⟨e, he, hh⟩)
    · exact Or.inl hn
    · exact Or.inr ⟨z, mu_flip_membership.mpr
        ⟨(u ++ z).length, le_rfl, by simpa only [List.take_length] using hz⟩⟩
    · exact Or.inr ⟨[], mu_flip_membership.mpr ⟨e, by simpa using he, by simpa using hh⟩⟩

/-- Any earlier prefix of a nonempty upper run is nonempty. -/
theorem P_nonempty_prefix {p : V × Bool} {u v : List (Fin n)}
    (hp : u.IsPrefix v) (h : (Automata.P (signedSys c χ) p v).Nonempty) :
    (Automata.P (signedSys c χ) p u).Nonempty := by
  obtain ⟨z, rfl⟩ := hp
  by_contra hn
  have he := P_nil_absorb (Finset.not_nonempty_iff_eq_empty.mp hn) z
  simp [he] at h

/-- A proper prefix of any nonempty upper run already reaches a negative unit. -/
theorem P_proper_prefix_neg {p : V × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.P (signedSys c χ) p γ).Nonempty) (hi : i < γ.length) :
    (Automata.P (signedSys c χ) p (γ.take i) ∩ NegDown c χ).Nonempty := by
  have hnext := P_nonempty_prefix (List.take_prefix (i + 1) γ) h
  rw [List.take_succ_eq_append_getElem hi] at hnext
  obtain ⟨r, hr, hn⟩ := popRoot hnext
  exact ⟨r, Finset.mem_inter.mpr ⟨hr,
    mem_NegDown.mpr ⟨(r.1, r.2, []), hn, Automata.d_refl _ _⟩⟩⟩

/-- Unit-dead seeds cannot be live. -/
theorem deadT_not_live {p : V × Bool} {u : List (Fin n)} (h : DeadT c χ p u) :
    ¬ Live c χ (p.1, p.2, u) := by
  rintro ⟨S, hS, hp⟩
  rcases h with hn | ⟨δ, hδ⟩
  · obtain ⟨n, hn, hr⟩ := reach_neg_iff.mpr hn
    exact hS.avoids (hr.mem_of_closed hS.closed hp) hn
  · exact hS.consistent.not_flip
      ((reach_extend p.1 p.2 u δ).mem_of_closed hS.closed hp) (mu_subset hS hδ)

/-- Overshooting a unit-unsupported cut leaves the upper automaton empty. -/
theorem cone {p : V × Bool} {u : List (Fin n)} {J j : ℕ}
    (hJ : ¬ DeadT c χ p (u.take J)) (hj : J < j) (hju : j ≤ u.length) :
    Automata.P (signedSys c χ) p (u.take j) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro h
  have hn := P_proper_prefix_neg h (show J < (u.take j).length by simp; omega)
  apply hJ
  exact Or.inl ⟨[], by simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hn⟩

/-- In a unit-unsupported source, a nonempty upper cut cannot consume an extension. -/
theorem cut_le_of_not_deadT {p : V × Bool} {u α : List (Fin n)} {i : ℕ}
    (hdead : ¬ DeadT c χ p u) (hi : i ≤ (u ++ α).length)
    (hp : (Automata.P (signedSys c χ) p ((u ++ α).take i)).Nonempty) :
    i ≤ u.length := by
  by_contra hn
  have hh := P_proper_prefix_neg hp
    (show u.length < ((u ++ α).take i).length by
      rw [List.length_take, Nat.min_eq_left hi]; omega)
  apply hdead
  exact Or.inl ⟨[], by
    simpa [List.take_take, Nat.min_eq_left (by omega : u.length ≤ i)] using hh⟩

/-- Prefix cuts give structural reachability, without a liveness assumption. -/
theorem reach_of_cuts {p q : V × Bool} {u t : List (Fin n)} {i e : ℕ}
    (hi : i ≤ u.length) (he : e ≤ t.length)
    (hpre : (u.drop i).IsPrefix (t.drop e))
    (hg : (Automata.P (signedSys c χ) p (u.take i) ∩
      Automata.Q (signedSys c χ) q (t.take e)).Nonempty) :
    Reach c χ (p.1, p.2, u) (q.1, q.2, t) := by
  obtain ⟨α, hα⟩ := hpre
  apply reach_iff_moves.mpr
  refine ⟨α, lowest_point_leaf.mpr ⟨i, by simp; omega, e, he, ?_, ?_⟩⟩
  · simpa [List.drop_append_of_le_length hi] using hα
  · simpa [List.take_append_of_le_length hi] using hg

/-- For an unblocked seed, reachability is characterized by word cuts. -/
theorem reach_iff_cuts_of_not_deadT {p q : V × Bool} {u t : List (Fin n)}
    (hd : ¬ DeadT c χ p u) :
    Reach c χ (p.1, p.2, u) (q.1, q.2, t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.P (signedSys c χ) p (u.take i) ∩
          Automata.Q (signedSys c χ) q (t.take e)).Nonempty := by
  constructor
  · intro hr
    obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
    obtain ⟨i, hi, e, he, hdrops, r, hr⟩ := lowest_point_leaf.mp hα
    obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
    have hib := cut_le_of_not_deadT hd hi ⟨r, hp⟩
    refine ⟨i, hib, e, he, ⟨α, ?_⟩, r, Finset.mem_inter.mpr ⟨?_, hq⟩⟩
    · simpa [List.drop_append_of_le_length hib] using hdrops
    · simpa [List.take_append_of_le_length hib] using hp
  · rintro ⟨i, hi, e, he, hp, hg⟩
    exact reach_of_cuts hi he hp hg

/-- Singleton closure of a live seed has a cut-based characterization. -/
theorem cl_membership_live {p q : V} {s s' : Bool} {u t : List (Fin n)}
    (hlive : Live c χ (p, s, u)) :
    (q, s', t) ∈ Cl c χ (p, s, u) ↔ (q, s', t) ∈ Mu c χ ∨
      ∃ i ≤ u.length, ∃ e ≤ t.length, (u.drop i).IsPrefix (t.drop e) ∧
        (Automata.P (signedSys c χ) (p, s) (u.take i) ∩
          Automata.Q (signedSys c χ) (q, s') (t.take e)).Nonempty := by
  rw [mem_cl, reach_iff_cuts_of_not_deadT (p := (p, s)) (q := (q, s'))
    (fun h => deadT_not_live h hlive)]

omit [Fintype V] in
/-- The self guard is symmetric, despite its presentation as one flipped intersection. -/
theorem flip_inter_symm {A B : Finset (V × Bool)} :
    (A ∩ B.map flipEmb).Nonempty ↔ (B ∩ A.map flipEmb).Nonempty := by
  have turn {A B : Finset (V × Bool)} (h : (A ∩ B.map flipEmb).Nonempty) :
      (B ∩ A.map flipEmb).Nonempty := by
    obtain ⟨r, hr⟩ := h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hr
    exact ⟨flipV r, Finset.mem_inter.mpr ⟨mem_map_flip.mp hb,
      mem_map_flip.mpr (by simpa using ha)⟩⟩
  exact ⟨turn, turn⟩

/-- A self guard cannot occur at equal cuts of an unblocked word. -/
theorem self_guard_ne {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (hg : (Automata.P (signedSys c χ) p (u.take i) ∩
      (Automata.P (signedSys c χ) p (u.take j)).map flipEmb).Nonempty) : i ≠ j := by
  rintro rfl
  obtain ⟨r, hr⟩ := hg
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hr
  have h₁ := sign_coherent hp
  have h₂ := sign_coherent (mem_map_flip.mp hq)
  change (!r.2) = _ at h₂
  rw [← h₁] at h₂
  cases r.2 <;> simp at h₂

/-- A self event yields a return to an opposite signed extension. -/
theorem selfEv_return {p : V × Bool} {u : List (Fin n)} {i j : ℕ}
    (h : SelfEv c χ p u i j) :
    ∃ δ, Reach c χ (p.1, p.2, u) (p.1, !p.2, u ++ δ) := by
  obtain ⟨hij, hj, ⟨δ, hδ⟩, hg⟩ := h
  refine ⟨δ, reach_of_cuts (p := p) (q := flipV p) (i := i)
    (Nat.le_trans (Nat.le_of_lt hij) hj)
    (show j ≤ (u ++ δ).length by simp; omega) ?_ ?_⟩
  · rw [List.drop_append_of_le_length hj, hδ]
  · rw [List.take_append_of_le_length hj, Q_flip]
    exact hg

/-- The two extended suffixes of a return have comparable original suffixes. -/
theorem return_selfEv_of_not_deadT {p : V × Bool} {u δ : List (Fin n)}
    (hd : ¬ DeadT c χ p u)
    (hr : Reach c χ (p.1, p.2, u) (p.1, !p.2, u ++ δ)) :
    ∃ i j, SelfEv c χ p u i j := by
  obtain ⟨α, hα⟩ := reach_iff_moves.mp hr
  obtain ⟨i, hi, j, hj, heq, r, hg⟩ := lowest_point_leaf.mp hα
  obtain ⟨hp, hq⟩ := Finset.mem_inter.mp hg
  change r ∈ Automata.Q (signedSys c χ) (flipV p) ((u ++ δ).take j) at hq
  rw [Q_flip, mem_map_flip] at hq
  have hib := cut_le_of_not_deadT hd hi ⟨r, hp⟩
  have hjb := cut_le_of_not_deadT hd hj ⟨flipV r, hq⟩
  rw [List.take_append_of_le_length hib] at hp
  rw [List.take_append_of_le_length hjb] at hq
  rw [List.drop_append_of_le_length hib, List.drop_append_of_le_length hjb] at heq
  have guard : (Automata.P (signedSys c χ) p (u.take i) ∩
      (Automata.P (signedSys c χ) p (u.take j)).map flipEmb).Nonempty :=
    ⟨r, Finset.mem_inter.mpr ⟨hp, mem_map_flip.mpr hq⟩⟩
  have hne := self_guard_ne guard
  have pi : (u.drop i).IsPrefix (u.drop i ++ α) := List.prefix_append _ _
  have pj : (u.drop j).IsPrefix (u.drop i ++ α) := heq.symm ▸ List.prefix_append _ _
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ⟨i, j, hij, hjb,
      List.prefix_of_prefix_length_le pj pi (by simp; omega), guard⟩
  · exact ⟨j, i, hji, hib,
      List.prefix_of_prefix_length_le pi pj (by simp; omega), flip_inter_symm.mp guard⟩

/-- Deadness is unit deadness or a strict self event. -/
theorem dead_iff_unit_or_self
    (hsat : Avoids χ (Mu c χ) ∧ Consistent (Mu c χ))
    {p : V × Bool} {u : List (Fin n)} :
    ¬ Live c χ (p.1, p.2, u) ↔
      DeadT c χ p u ∨ ∃ i j, SelfEv c χ p u i j := by
  classical
  rw [dead_iff hsat]
  constructor
  · rintro (hn | hm | ⟨δ, hr⟩)
    · exact Or.inl (Or.inl (reach_neg_iff.mp hn))
    · exact Or.inl (Or.inr hm)
    · by_cases hd : DeadT c χ p u
      · exact Or.inl hd
      · exact Or.inr (return_selfEv_of_not_deadT hd hr)
  · rintro ((hn | hm) | ⟨i, j, hs⟩)
    · exact Or.inl (reach_neg_iff.mpr hn)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (selfEv_return hs))

section Visible
variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-- A visible seed reaches a negative consequent unit. -/
def DeadU (p : X × Bool) (u : List (Fin n)) : Prop :=
  ∃ z, (Automata.P (signedSys c ψ) (.inl p.1, p.2) (u ++ z) ∩ NegDown c ψ).Nonempty

/-- Consequent unit deadness is an upper-state test. -/
theorem deadU_iff_state (p : X × Bool) (u : List (Fin n)) :
    DeadU c ψ p u ↔ negReachS c ψ (Automata.P (signedSys c ψ) (.inl p.1, p.2) u) := by
  rw [negReachS_iff]; simp only [upperRun_P, DeadU]

/-- Consequent unit deadness is reachability to a forbidden unit. -/
theorem deadU_iff_reach_neg (p : X × Bool) (u : List (Fin n)) :
    DeadU c ψ p u ↔ ∃ n, Neg ψ n ∧ Reach c ψ (.inl p.1, p.2, u) n :=
  reach_neg_iff.symm

variable {c φ ψ}

/-- Consequent unit deadness descends to prefixes. -/
theorem deadU_prefix {p : X × Bool} {u v : List (Fin n)} :
    DeadU c ψ p (u ++ v) → DeadU c ψ p u := by
  rintro ⟨z, hz⟩
  exact ⟨v ++ z, by simpa [List.append_assoc] using hz⟩

/-- The unit condition excludes live seeds with consequent unit deadness. -/
theorem condU_iff : CondU c φ ψ ↔
    ∀ x s u, DeadU c ψ (x, s) u → ¬ Live c φ (x, s, u) := by
  constructor
  · intro h x s u hd hl
    obtain ⟨n, hn, hr⟩ := (deadU_iff_reach_neg c ψ (x, s) u).mp hd
    exact h (x, s, u) hl n hn hr
  · intro h ⟨x, s, u⟩ hl n hn hr
    exact h x s u ((deadU_iff_reach_neg c ψ (x, s) u).mpr ⟨n, hn, hr⟩) hl

/-- A head event before supported rejection forces consequent unit deadness. -/
theorem head_prefix_deadU {p : X × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.P (signedSys c ψ) (.inl p.1, p.2) γ).Nonempty)
    (hi : i < γ.length) : DeadU c ψ p (γ.take i) :=
  ⟨[], by simpa using P_proper_prefix_neg h hi⟩

/-- Shared state type for extraction and the unit reader. -/
abbrev TargetState (X Z : Type*) :=
  Finset (X × Bool) × Bool × Finset ((X ⊕ Z) × Bool)

variable (c φ ψ)

/-- Track both upper summaries and the antecedent past-collision flag. -/
def targetDFA (p : X × Bool) : LDFA (Fin n) (TargetState X Z) where
  start := (Automata.up (signedSys c φ) p,
    decide (flipHitS c φ (Automata.up (signedSys c φ) p)),
    Automata.up (signedSys c ψ) (.inl p.1, p.2))
  step S b :=
    let P := Automata.pstep (signedSys c φ) S.1 b
    (P, S.2.1 || decide (flipHitS c φ P), Automata.pstep (signedSys c ψ) S.2.2 b)

/-- Antecedent unit deadness tested on a target-reader state. -/
def targetDeadT (S : TargetState X Z) : Prop :=
  S.2.1 = true ∨ negReachS c φ S.1 ∨ muReachS c φ S.1

/-- Consequent unit deadness tested on a target-reader state. -/
def targetDeadU (S : TargetState X Z) : Prop := negReachS c ψ S.2.2

/-- The antecedent test on target-reader states is decidable. -/
instance (S : TargetState X Z) : Decidable (targetDeadT c φ S) := by
  unfold targetDeadT; infer_instance
/-- The consequent test on target-reader states is decidable. -/
instance (S : TargetState X Z) : Decidable (targetDeadU c ψ S) := by
  unfold targetDeadU; infer_instance

/-- States avoiding both antecedent and consequent unit deadness. -/
def targetRej : Finset (TargetState X Z) := Finset.univ.filter fun S =>
  ¬ targetDeadT c φ S ∧ ¬ targetDeadU c ψ S

/-- States with consequent unit deadness but no antecedent unit deadness. -/
def targetUnit : Finset (TargetState X Z) := Finset.univ.filter fun S =>
  ¬ targetDeadT c φ S ∧ targetDeadU c ψ S

/-- State pairs with intersecting opposite signed antecedent summaries. -/
def targetSelfGuard : Finset (TargetState X Z × TargetState X Z) :=
  Finset.univ.filter fun S => (S.1.1 ∩ S.2.1.map flipEmb).Nonempty

variable {c φ ψ}

private theorem flipHits_snoc {p : X × Bool} {u : List (Fin n)} {b : Fin n} :
    (∃ e ≤ (u ++ [b]).length,
      flipHitS c φ (Automata.P (signedSys c φ) p ((u ++ [b]).take e))) ↔
    (∃ e ≤ u.length, flipHitS c φ (Automata.P (signedSys c φ) p (u.take e))) ∨
      flipHitS c φ (Automata.P (signedSys c φ) p (u ++ [b])) := by
  constructor
  · rintro ⟨e, he, hh⟩
    by_cases h : e ≤ u.length
    · exact Or.inl ⟨e, h, by simpa [List.take_append_of_le_length h] using hh⟩
    · have heq : e = (u ++ [b]).length := by simp at he ⊢; omega
      subst e
      exact Or.inr (by simpa only [List.take_length] using hh)
  · rintro (⟨e, he, hh⟩ | hh)
    · exact ⟨e, by simp; omega, by simpa [List.take_append_of_le_length he] using hh⟩
    · exact ⟨(u ++ [b]).length, le_rfl, by simpa only [List.take_length] using hh⟩

/-- The target run records both summaries and every earlier sign hit. -/
theorem targetDFA_run (p : X × Bool) (u : List (Fin n)) :
    ((targetDFA c φ ψ p).run u).1 = Automata.P (signedSys c φ) p u ∧
    (((targetDFA c φ ψ p).run u).2.1 = true ↔
      ∃ e ≤ u.length, flipHitS c φ (Automata.P (signedSys c φ) p (u.take e))) ∧
    ((targetDFA c φ ψ p).run u).2.2 = Automata.P (signedSys c ψ) (.inl p.1, p.2) u := by
  induction u using List.reverseRecOn with
  | nil => simp [targetDFA, LDFA.run, LDFA.runFrom]
  | append_singleton u b ih =>
    have hs : (targetDFA c φ ψ p).run (u ++ [b]) =
        (targetDFA c φ ψ p).step ((targetDFA c φ ψ p).run u) b := by
      simp [LDFA.run, LDFA.runFrom, List.foldl_append]
    rw [hs]
    change Automata.pstep (signedSys c φ) _ b = _ ∧
      ((_ || decide (flipHitS c φ (Automata.pstep (signedSys c φ) _ b))) = true ↔ _) ∧
      Automata.pstep (signedSys c ψ) _ b = _
    rw [ih.1, ih.2.2, ← Automata.P_snoc, ← Automata.P_snoc]
    refine ⟨rfl, ?_, rfl⟩
    rw [Bool.or_eq_true, decide_eq_true_eq, ih.2.1, flipHits_snoc]

/-- The target-state antecedent test characterizes unit deadness. -/
theorem targetDFA_deadT (p : X × Bool) (u : List (Fin n)) :
    targetDeadT c φ ((targetDFA c φ ψ p).run u) ↔ DeadT c φ p u := by
  rw [targetDeadT, (targetDFA_run p u).1, (targetDFA_run p u).2.1, deadT_iff_state]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- The target-state consequent test characterizes unit deadness. -/
theorem targetDFA_deadU (p : X × Bool) (u : List (Fin n)) :
    targetDeadU c ψ ((targetDFA c φ ψ p).run u) ↔ DeadU c ψ p u := by
  rw [targetDeadU, (targetDFA_run p u).2.2, deadU_iff_state]

/-- Target rejection means that neither unit-deadness test holds. -/
theorem targetDFA_rej (p : X × Bool) (u : List (Fin n)) :
    (targetDFA c φ ψ p).run u ∈ targetRej c φ ψ ↔
      ¬ DeadT c φ p u ∧ ¬ DeadU c ψ p u := by
  simp only [targetRej, Finset.mem_filter, Finset.mem_univ, true_and,
    targetDFA_deadT, targetDFA_deadU]

/-- Unit targets have consequent unit deadness without antecedent unit deadness. -/
theorem targetDFA_unit (p : X × Bool) (u : List (Fin n)) :
    (targetDFA c φ ψ p).run u ∈ targetUnit c φ ψ ↔
      ¬ DeadT c φ p u ∧ DeadU c ψ p u := by
  simp only [targetUnit, Finset.mem_filter, Finset.mem_univ, true_and,
    targetDFA_deadT, targetDFA_deadU]

/-- The target self guard is opposite-sign summary intersection. -/
theorem targetDFA_selfGuard (p : X × Bool) (u : List (Fin n)) (i j : ℕ) :
    ((targetDFA c φ ψ p).atCut u i, (targetDFA c φ ψ p).atCut u j) ∈
        targetSelfGuard (X := X) (Z := Z) ↔
      (Automata.P (signedSys c φ) p (u.take i) ∩
        (Automata.P (signedSys c φ) p (u.take j)).map flipEmb).Nonempty := by
  simp only [targetSelfGuard, Finset.mem_filter, Finset.mem_univ, true_and,
    LDFA.atCut, (targetDFA_run p (u.take i)).1, (targetDFA_run p (u.take j)).1]

/-- The cut state records prefix summaries and earlier sign hits. -/
theorem targetDFA_atCut (p : X × Bool) (u : List (Fin n)) (j : ℕ) :
    ((targetDFA c φ ψ p).atCut u j).1 = Automata.P (signedSys c φ) p (u.take j) ∧
    (((targetDFA c φ ψ p).atCut u j).2.1 = true ↔
      ∃ e ≤ min j u.length, flipHitS c φ (Automata.P (signedSys c φ) p (u.take e))) ∧
    ((targetDFA c φ ψ p).atCut u j).2.2 =
      Automata.P (signedSys c ψ) (.inl p.1, p.2) (u.take j) := by
  obtain ⟨hp, hf, hq⟩ := targetDFA_run (c := c) (φ := φ) (ψ := ψ) p (u.take j)
  refine ⟨hp, ?_, hq⟩
  rw [LDFA.atCut, hf]
  simp only [List.length_take, List.take_take]
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e, he, by simpa [Nat.min_eq_left (le_trans he (Nat.min_le_left _ _))] using hh⟩
  · rintro ⟨e, he, hh⟩
    exact ⟨e, he, by simpa [Nat.min_eq_left (le_trans he (Nat.min_le_left _ _))] using hh⟩

/-- Rejection at a cut is absence of both unit-deadness predicates. -/
theorem targetDFA_rej_atCut (p : X × Bool) (u : List (Fin n)) (j : ℕ) :
    (targetDFA c φ ψ p).atCut u j ∈ targetRej c φ ψ ↔
      ¬ DeadT c φ p (u.take j) ∧ ¬ DeadU c ψ p (u.take j) :=
  targetDFA_rej p (u.take j)

/-- A unit target at a cut detects consequent-only unit deadness. -/
theorem targetDFA_unit_atCut (p : X × Bool) (u : List (Fin n)) (j : ℕ) :
    (targetDFA c φ ψ p).atCut u j ∈ targetUnit c φ ψ ↔
      ¬ DeadT c φ p (u.take j) ∧ DeadU c ψ p (u.take j) :=
  targetDFA_unit p (u.take j)

end Visible

end DeciENSSE.Core.Mixed
