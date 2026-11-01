import DeciENSSE.Core.Mixed.Membership
import DeciNSSE.RejectedTail.Decision

/-! # Deciding the mixed unit condition

Live counterexamples to the unit condition are rejected-path reader holes.
The elementary finite search includes epsilon and the empty alphabet.

## Main declarations

- `unitReader`, `unit_absHole_iff`, `unit_between`,
  `unit_cone`, `unitRejectedPath`, `condU_iff_no_unit_holes`, `decideCondU`.
-/

namespace DeciENSSE.Core.Mixed
open DeciENSSE.Core.Words

variable {n : ℕ}
open DeciENSSE.Core.Full DeciNSSE.Holes DeciNSSE.RejectedTail

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
variable (c : Fin n → Bool) (φ : List (LitT n X)) (ψ : List (LitT n (X ⊕ Z)))

/-- Read the shared B-automaton directly over `Fin n`. -/
def unitReader (p : X × Bool) : DFA (Fin n) (TargetState X Z) where
  start := (targetDFA c φ ψ p).start
  step q a := (targetDFA c φ ψ p).step q a
  accept := ∅

/-- The same self guard as in the extracted two-word instance. -/
def unitRelation (a b : TargetState X Z) : Prop := (a, b) ∈ targetSelfGuard

/-- The finite predicate has a computable decision. -/
instance (a b : TargetState X Z) : Decidable (unitRelation a b) := by
  exact decidable_of_iff ((a.1 ∩ b.1.map flipEmb).Nonempty)
    (by simp [unitRelation, targetSelfGuard])

/-- Unit-free in φ, but able to reach a negative unit in ψ. -/
def unitTarget : Set (TargetState X Z) := ↑(targetUnit c φ ψ)

/-- The finite predicate has a computable decision. -/
instance (q : TargetState X Z) : Decidable (q ∈ unitTarget c φ ψ) :=
  inferInstanceAs (Decidable (q ∈ targetUnit c φ ψ))

/-- The reader and target automaton have identical runs. -/
theorem unitReader_eval (p : X × Bool) (w : List (Fin n)) :
    (unitReader c φ ψ p).eval w = (targetDFA c φ ψ p).run w := rfl

/-- Reader targets are consequent-only unit deadness. -/
theorem unitReader_target (p : X × Bool) (w : List (Fin n)) :
    (unitReader c φ ψ p).eval w ∈ unitTarget c φ ψ ↔
      ¬ DeadT c φ p w ∧ DeadU c ψ p w := by
  rw [unitReader_eval]
  exact targetDFA_unit p w

/-- The reader guard compares opposite signed antecedent summaries. -/
theorem unitReader_guard (p : X × Bool) (w : List (Fin n)) (i j : ℕ) :
    unitRelation ((unitReader c φ ψ p).eval (w.take i))
      ((unitReader c φ ψ p).eval (w.take j)) ↔
    (Automata.P (signedSys c φ) p (w.take i) ∩
      (Automata.P (signedSys c φ) p (w.take j)).map flipEmb).Nonempty := by
  simp only [unitRelation, unitReader_eval]
  exact targetDFA_selfGuard p w i j

/-- Self events are exactly admitted strict prefix comparisons. -/
theorem unit_selfEv_iff (p : X × Bool) (w : List (Fin n)) (i j : ℕ) :
    SelfEv c φ p w i j ↔ i < j ∧ j ≤ w.length ∧
      (w.drop j).IsPrefix (w.drop i) ∧
      unitRelation ((unitReader c φ ψ p).eval (w.take i))
        ((unitReader c φ ψ p).eval (w.take j)) := by
  rw [SelfEv, unitReader_guard]

/-- The unit reader's holes are exactly the live counterexamples to (U). -/
theorem unit_absHole_iff (hφ : ∃ ρ, SatT c ρ φ) (p : X × Bool)
    (w : List (Fin n)) :
    IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w ↔
      DeadU c ψ p w ∧ Live c φ (p.1, p.2, w) := by
  classical
  rw [isReaderHole_iff, unitReader_target]
  constructor
  · rintro ⟨⟨hd, hu⟩, hn⟩
    refine ⟨hu, ?_⟩
    by_contra hl
    rcases (dead_iff_unit_or_self (sat_iff_mu.mp hφ)).mp hl with ht | ⟨i,j,he⟩
    · exact hd ht
    · obtain ⟨hij,hj,hpre,hg⟩ := (unit_selfEv_iff c φ ψ p w i j).mp he
      exact hn i j hij hj hpre hg
  · rintro ⟨hu, hl⟩
    refine ⟨⟨fun hd => deadT_not_live hd hl, hu⟩, ?_⟩
    intro i j hij hj hpre hg
    apply (dead_iff_unit_or_self (sat_iff_mu.mp hφ)).mpr (Or.inr ?_) hl
    exact ⟨i,j,(unit_selfEv_iff c φ ψ p w i j).mpr ⟨hij,hj,hpre,hg⟩⟩

/-- The complement of DeadT is extension closed, and DeadU is prefix closed. -/
theorem unit_between (p : X × Bool) (v u w : List (Fin n))
    (hvu : v.IsPrefix u) (huw : u.IsPrefix w)
    (hv : (unitReader c φ ψ p).eval v ∈ unitTarget c φ ψ)
    (hw : (unitReader c φ ψ p).eval w ∈ unitTarget c φ ψ) :
    (unitReader c φ ψ p).eval u ∈ unitTarget c φ ψ := by
  apply (unitReader_target c φ ψ p u).mpr
  obtain ⟨hv, _⟩ := (unitReader_target c φ ψ p v).mp hv
  obtain ⟨_, hw⟩ := (unitReader_target c φ ψ p w).mp hw
  constructor
  · obtain ⟨z, rfl⟩ := hvu
    exact fun h => hv (deadT_prefix (by simpa using h))
  · obtain ⟨z, rfl⟩ := huw
    exact deadU_prefix (by simpa using hw)

/-- Every admitted pair ends before any unit target cut, hence before the first. -/
theorem unit_cone (p : X × Bool) :
    AdmissionCone (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) := by
  intro w J _ hJ i j _ hj _ hg
  have hd := ((unitReader_target c φ ψ p (w.take J)).mp hJ.2.1).1
  have hg := (unitReader_guard c φ ψ p w i j).mp hg
  obtain ⟨q,hq⟩ := flip_inter_symm.mp hg
  have hp := (Finset.mem_inter.mp hq).1
  by_contra hn
  have he := cone hd (by omega : J < j) (by simpa using hj)
  rw [he] at hp
  exact Finset.notMem_empty q hp

/-- Unit targets and guards satisfy the rejected-path laws. -/
instance unitRejectedPath (p : X × Bool) :
    RejectedPath (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) where
  between := unit_between c φ ψ p
  cone := unit_cone c φ ψ p

/-- The unit condition holds exactly when every unit reader is hole-free. -/
theorem condU_iff_no_unit_holes (hφ : ∃ ρ, SatT c ρ φ) :
    CondU c φ ψ ↔ ∀ p w,
      ¬ IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w := by
  rw [condU_iff]
  constructor
  · intro h p w hh
    obtain ⟨hu,hl⟩ := (unit_absHole_iff c φ ψ hφ p w).mp hh
    exact h p.1 p.2 w hu hl
  · intro h x s u hu hl
    exact h (x,s) u ((unit_absHole_iff c φ ψ hφ (x,s) u).mpr ⟨hu,hl⟩)

/-- Epsilon has no strict cut pairs. -/
theorem unit_empty_hole_iff (p : X × Bool) :
    IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) [] ↔
      (unitReader c φ ψ p).start ∈ unitTarget c φ ψ := by
  rw [isReaderHole_iff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro s e hse he
    simp only [List.length_nil] at he
    omega

/-- Decide an epsilon hole by testing the initial target state. -/
instance unitEmptyHoleDecidable (p : X × Bool) :
    Decidable (IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) []) :=
  decidable_of_iff _ (unit_empty_hole_iff c φ ψ p).symm

/-- Executable generic finite search, including epsilon and the empty alphabet. -/
def decideUnitHole (p : X × Bool) :
    Decidable (∃ w, IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w) :=
  DeciNSSE.RejectedTail.decideHole _ _ _

/-- The unit-condition decision, requiring only satisfiability of the antecedent. -/
def decideCondU (hφ : ∃ ρ, SatT c ρ φ) : Decidable (CondU c φ ψ) := by
  letI (p : X × Bool) := decideUnitHole c φ ψ p
  apply decidable_of_iff
    (∀ p, ¬ ∃ w, IsReaderHole (unitReader c φ ψ p) unitRelation (unitTarget c φ ψ) w)
  simpa only [not_exists] using (condU_iff_no_unit_holes c φ ψ hφ).symm

/-- The unit decision returns true exactly when the condition holds. -/
theorem decideCondU_correct (hφ : ∃ ρ, SatT c ρ φ) :
    @decide (CondU c φ ψ) (decideCondU c φ ψ hφ) = true ↔ CondU c φ ψ :=
  @decide_eq_true_iff _ (decideCondU c φ ψ hφ)

end DeciENSSE.Core.Mixed
