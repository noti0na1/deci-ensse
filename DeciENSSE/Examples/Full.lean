import DeciENSSE.Core.Full.AC
import DeciENSSE.Core.Full.Observations
import DeciENSSE.Core.Full.Classes
import DeciENSSE.Core.Full.ACPins
import DeciENSSE.Core.Full.Flatten
import DeciENSSE.Core.Full.PinningSpines
import DeciENSSE.Core.Full.PinningGround
import DeciENSSE.Core.Full.Pinning
import DeciENSSE.Core.Full.TopGraphs

/-! # Full-signature examples

Concrete trees, observations, pins, and entailment decisions exercise the library.

## Main declarations

The example namespaces below give unary, ternary, and nullary instances.
-/

namespace DeciENSSE.Core.Full.AC
open DeciNSSE

variable {n : ℕ}

namespace ACExamples

/-- The third child is observed directly, without a binary path encoding. -/
theorem ternary_third_child :
    aobs (DeciNSSE.Tree.node ![DeciNSSE.Tree.bot, DeciNSSE.Tree.bot, DeciNSSE.Tree.top]) [2] ∧
      [2] ∈ (cobs (DeciNSSE.Tree.node
        ![DeciNSSE.Tree.bot, DeciNSSE.Tree.bot, DeciNSSE.Tree.top])).carrier := by
  constructor
  · simp [aobs, Safety.hasLabel_node_cons _ _ _ Sym.top (by decide)]
  · simp

end ACExamples

end DeciENSSE.Core.Full.AC

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace ObservationExamples

/-- At child two, top has C and A; the dual-C observation is therefore false. -/
theorem ternary_flags :
    let ρ : Unit → DeciNSSE.Tree 3 := fun _ => DeciNSSE.Tree.node ![DeciNSSE.Tree.bot,
      DeciNSSE.Tree.bot, DeciNSSE.Tree.top]
    (⟨false, (), [2], true⟩ : Observation 3 Unit).Holds ρ ∧
      (⟨true, (), [2], false⟩ : Observation 3 Unit).Holds ρ := by
  simp [Observation.Holds]

/-- Both directions of a ground bound can pin the same finite tree. -/
theorem ground_bounds_nonvacuous (g : FTree n) :
    (⟨(), true, g⟩ : GroundBound n Unit).Holds (fun _ => false) (fun _ => g.toTree) ∧
      (⟨(), false, g⟩ : GroundBound n Unit).Holds (fun _ => false) (fun _ => g.toTree) :=
  ⟨DeciNSSE.treeLe_refl _ _, DeciNSSE.treeLe_refl _ _⟩

end ObservationExamples

end DeciENSSE.Core.Full

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace TopExamples

/-- Top has a finite presentation. -/
theorem finite_top : FiniteTop (DeciNSSE.Tree.top : DeciNSSE.Tree n) := ⟨FTree.top, rfl⟩

/-- Top has a regular presentation. -/
theorem regular_top : RegularTop (DeciNSSE.Tree.top : DeciNSSE.Tree n) := by
  apply (Characterization.unfold_range_iff _).mpr
  exact Characterization.subtrees_finite_of_domain_finite _
    (Characterization.domain_toTree_finite FTree.top)

/-- A satisfiable ternary system meets the finite pinning premise. -/
theorem finite_pinning_nonvacuous :
    SatisfiableIn FiniteTop (fun _ => false) ([.top ()] : List (LitT 3 Unit)) ∧
      FiniteBoundPinning ([.top ()] : List (LitT 3 Unit)) := by
  constructor
  · exact ⟨fun _ => DeciNSSE.Tree.top, fun _ => finite_top, by simp [SatT, HoldsT]⟩
  · rintro _ B ⟨ρ, hs, hb⟩
    refine ⟨ρ, ?_, hs, hb⟩
    intro v
    cases v
    have ht : ρ () = DeciNSSE.Tree.top := hs (.top ()) (by simp)
    rw [ht]
    exact finite_top

end TopExamples

end DeciENSSE.Core.Full

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace ACPinsExamples

/-- The third child is selected and both siblings are bottom. -/
theorem ternary_lower : ACPins.lower [2] (.top : FTree 3) =
    .node ![.bot, .bot, .top] := by
  simp only [ACPins.lower]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- There are no sibling fillers at arity one. -/
theorem unary_lower : ACPins.lower [0] (.top : FTree 1) =
    .node (fun _ => .top) := by
  simp only [ACPins.lower]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The two positive observations of a top third child yield valid bounds. -/
theorem ternary_bounds :
    let ρ : Unit → DeciNSSE.Tree 3 := fun _ => DeciNSSE.Tree.node ![DeciNSSE.Tree.bot,
      DeciNSSE.Tree.bot, DeciNSSE.Tree.top]
    (⟨false, (), [2], true⟩ : Observation 3 Unit).bound.Holds (fun _ => false) ρ ∧
      (⟨true, (), [2], false⟩ : Observation 3 Unit).bound.Holds (fun _ => false) ρ := by
  simp only [observation_bound]
  exact ObservationExamples.ternary_flags

end ACPinsExamples

end DeciENSSE.Core.Full

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace FlattenExamples

/-- Unary negative variance needs no off-spine fillers. -/
theorem unary_sandwich (u v : DeciNSSE.Tree 1) :
    DeciNSSE.Tree.Le (fun _ => true) (DeciNSSE.Tree.node (fun _ => v)) (DeciNSSE.Tree.node (fun _ =>
      u)) ↔
      DeciNSSE.Tree.Le (fun _ => true) u v := by
  have hv : Flatten.sandwichArgs (n := 1) v u = fun _ => v := by
    funext i; fin_cases i; rfl
  have hu : Flatten.sandwichArgs (n := 1) u u = fun _ => u := by
    funext i; fin_cases i; rfl
  simpa only [Bool.true_eq, ↓reduceIte, hv, hu] using
    Flatten.sandwich_iff (fun _ => true) u v

/-- Both off-spine slots remain equal, including the negative third slot. -/
theorem ternary_sandwich (u v : DeciNSSE.Tree 3) :
    DeciNSSE.Tree.Le ![true, false, true] (DeciNSSE.Tree.node ![v, u, u]) (DeciNSSE.Tree.node ![u,
      u, u]) ↔
      DeciNSSE.Tree.Le ![true, false, true] u v := by
  have hv : Flatten.sandwichArgs (n := 3) v u = ![v, u, u] := by
    funext i; fin_cases i <;> rfl
  have hu : Flatten.sandwichArgs (n := 3) u u = ![u, u, u] := by
    funext i; fin_cases i <;> rfl
  simpa only [Matrix.cons_val_zero, Bool.true_eq, ↓reduceIte, hv, hu] using
    Flatten.sandwich_iff ![true, false, true] u v

/-- A finite witness using all five literal forms and a strict inequality. -/
def sample (n : ℕ) : List (LitT n Bool) :=
  [.bot false, .top true, .le false true,
    .fle (fun _ => false) true, .lef false (fun _ => true)]

/-- The example constraint has a finite solution. -/
theorem sample_finite (c : Fin n → Bool) : SatFin c (sample n) := by
  refine ⟨fun b => if b then DeciNSSE.Tree.top else DeciNSSE.Tree.bot, ?_, ?_⟩
  · intro b
    cases b
    · exact ⟨FTree.bot, rfl⟩
    · exact ⟨FTree.top, rfl⟩
  · simp [sample, SatT, HoldsT]

/-- The sample example satisfies the finite realization conclusion. -/
theorem sample_flattened [NeZero n] (c : Fin n → Bool) {k : ℕ}
    (e : Flatten.Vars Bool ≃ Fin k) :
    ∃ τ : Fin k → FTree n,
      DeciNSSE.Sat c (FTree.toTree ∘ τ) (Flatten.flatten c e (sample n)) :=
  (Flatten.finite_iff c e _).mp (sample_finite c)

/-- The unary example satisfies the finite realization conclusion. -/
theorem unary_flattened {k : ℕ} (e : Flatten.Vars Bool ≃ Fin k) :
    ∃ τ : Fin k → FTree 1, DeciNSSE.Sat (fun _ => true) (FTree.toTree ∘ τ)
      (Flatten.flatten (fun _ => true) e (sample 1)) := sample_flattened _ e

/-- The ternary example satisfies the finite realization conclusion. -/
theorem ternary_flattened {k : ℕ} (e : Flatten.Vars Bool ≃ Fin k) :
    ∃ τ : Fin k → FTree 3, DeciNSSE.Sat ![true, false, true] (FTree.toTree ∘ τ)
      (Flatten.flatten ![true, false, true] e (sample 3)) := sample_flattened _ e

end FlattenExamples

end DeciENSSE.Core.Full

namespace DeciENSSE.Core.Full.Pinning
open DeciNSSE

variable {n : ℕ}

namespace SpineExamples

/-- All four pin kinds; the parameter can select any child, including slot 2. -/
def pins (i : Fin n) : List (PathPin n (Fin 2)) :=
  [⟨0, [], .noBot⟩, ⟨0, [], .noTop⟩, ⟨0, [i], .bot⟩, ⟨1, [], .top⟩]

/-- A finite assignment witnessing the displayed constraints and pins. -/
def assignment (n : ℕ) : Fin 2 → FTree n :=
  ![.node (fun _ => .bot), .top]

/-- The example assignment satisfies both the constraint and all path pins. -/
theorem sample_sat (i : Fin n) :
    Covariant.Sat (FTree.toTree ∘ assignment n) [.eqTop 1] ∧
      ∀ p ∈ pins i, p.Holds (FTree.toTree ∘ assignment n) := by
  simp [Covariant.Sat, Covariant.holds, pins, assignment, PathPin.Holds, PinKind.Holds]

/-- Non-vacuity of both premises of the finite realization theorem. -/
theorem sample_realized (i : Fin n) :
    ∃ σ : Fin 2 → FTree n, Covariant.Sat (FTree.toTree ∘ σ) [.eqTop 1] ∧
      ∀ p ∈ pins i, p.Holds (FTree.toTree ∘ σ) :=
  realize_pins (pins i) [.eqTop 1]
    ⟨assignment n, (sample_sat i).1⟩
    ⟨FTree.toTree ∘ assignment n, sample_sat i⟩

end SpineExamples

end DeciENSSE.Core.Full.Pinning

namespace DeciENSSE.Core.Full.Pinning
open DeciNSSE

variable {n : ℕ}

namespace GroundExamples

/-- Lower pins must inspect the third child as well as the first two. -/
theorem ternary_lower_pins :
    groundPins () true (.node ![.bot, .bot, .top] : FTree 3) =
      [⟨(), [], .noBot⟩, ⟨(), [2], .top⟩] := by
  simp [groundPins, List.finRange_succ, PathPin.prefix]

/-- Upper pins constrain both bottom siblings and exclude a top root. -/
theorem ternary_upper_pins :
    groundPins () false (.node ![.bot, .bot, .top] : FTree 3) =
      [⟨(), [], .noTop⟩, ⟨(), [0], .bot⟩, ⟨(), [1], .bot⟩] := by
  simp [groundPins, List.finRange_succ, PathPin.prefix]

/-- Both directions remain exact for the zero-child constructor. -/
theorem nullary_pins (lower : Bool) (t : DeciNSSE.Tree 0) :
    (∀ p ∈ groundPins () lower (.node Fin.elim0), p.Holds (fun _ => t)) ↔
      if lower then DeciNSSE.Tree.node Fin.elim0 ≤ t else t ≤ DeciNSSE.Tree.node Fin.elim0 := by
  have he : (fun i : Fin 0 => (Fin.elim0 i : FTree 0).toTree) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  simpa only [FTree.toTree_node, he] using
    groundPins_iff () lower (.node Fin.elim0) (fun _ => t)

end GroundExamples

end DeciENSSE.Core.Full.Pinning

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace PinningExamples

/-- A nonempty system on an infinite ambient carrier, including an inequality. -/
def sample (n : ℕ) : List (LitT n ℕ) :=
  [.bot 0, .le 0 1, .fle (fun _ => 0) 1]

/-- A finite assignment witnessing the displayed constraints and pins. -/
def assignment (g : FTree n) : ℕ → DeciNSSE.Tree n :=
  fun v => if v = 1 then g.toTree else DeciNSSE.Tree.bot

/-- Every value of the example assignment has a finite presentation. -/
theorem assignment_finite (g : FTree n) (v : ℕ) : FiniteTop (assignment g v) := by
  by_cases hv : v = 1
  · exact ⟨g, by simp [assignment, hv]⟩
  · exact ⟨.bot, by simp [assignment, hv]⟩

/-- The example assignment satisfies the displayed constraints. -/
theorem assignment_sat (a : Fin n → FTree n) :
    SatT (fun _ => false) (assignment (.node a)) (sample n) := by
  simp [sample, SatT, HoldsT, assignment, DeciNSSE.Tree.node_le_node_iff]

/-- The example constraint has a finite solution. -/
theorem sample_finite (n : ℕ) : SatisfiableIn FiniteTop (fun _ => false) (sample n) :=
  ⟨assignment (.node (fun _ => .bot)), assignment_finite _, assignment_sat _⟩

/-- Opposite bounds pin exactly the finite tree with top in the selected slot. -/
def bounds (i : Fin n) : List (GroundBound n ℕ) :=
  [⟨1, true, ACPins.lower [i] .top⟩, ⟨1, false, ACPins.lower [i] .top⟩]

/-- The example constraints and bounds have a common solution. -/
theorem sample_joint (i : Fin n) :
    ∃ ρ, SatT (fun _ => false) ρ (sample n) ∧ ∀ b ∈ bounds i, b.Holds (fun _ => false) ρ := by
  refine ⟨assignment (ACPins.lower [i] .top), assignment_sat _, ?_⟩
  simp [bounds, GroundBound.Holds, assignment]

/-- Both pinning premises have concrete witnesses; the carrier is ℕ. -/
theorem sample_realized [NeZero n] (i : Fin n) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ (sample n) ∧
      ∀ b ∈ bounds i, b.Holds (fun _ => false) τ :=
  finiteBoundPinning (sample n) (sample_finite n) (bounds i) (sample_joint i)

end PinningExamples

end DeciENSSE.Core.Full

namespace DeciENSSE.Core.Full.TopGraphs
open DeciNSSE

variable {n : ℕ} {I V : Type*}

namespace GraphExamples

/-- The third child differs from the first two, exercising all n-ary slots. -/
def ternaryGraph : RGraph 3 where
  size := 3
  root := 0
  label := ![.f, .bot, .top]
  child := fun _ => ![1, 1, 2]

/-- Every model of the graph equations sees top at the third child. -/
theorem ternary_third_child {τ : States (fun _ : Unit => ternaryGraph) → DeciNSSE.Tree 3}
    (h : Model (fun _ : Unit => ternaryGraph) τ) :
    (τ ⟨(), ternaryGraph.root⟩).fn [2] = some Sym.top := by
  rw [model_unique _ h]
  rfl

/-- Simultaneous lower and upper bindings retain the designated graph root. -/
theorem ternary_regularize :
    ∃ τ : Unit → DeciNSSE.Tree 3, (∀ v, ∃ g : RGraph 3, g.unfold = τ v) ∧
      τ () = ternaryGraph.unfold := by
  obtain ⟨τ, hc, _, hb⟩ := regularize (fun _ => false) ([] : List (LitT 3 Unit))
    (fun _ : Unit => ternaryGraph) [((), (), true), ((), (), false)]
    ⟨fun _ => ternaryGraph.unfold, by simp [SatT], by simp [bindingHolds, DeciNSSE.treeLe_refl]⟩
  exact ⟨τ, hc, DeciNSSE.treeLe_antisymm (hb ((), (), false) (by simp))
    (hb ((), (), true) (by simp))⟩

end GraphExamples

end DeciENSSE.Core.Full.TopGraphs
