import DeciENSSE.Core.Full.PinningGround
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Tree

/-! # Finite bound pinning

Restricting to the finitely many variables occurring in the constraints and
bounds extends finite realization to an arbitrary variable type.

## Main declarations

- `finiteBoundPinning`
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ}

namespace Pinning

/-- List the variables occurring in a flat literal. -/
def vars {V : Type*} : LitT n V → List V
  | .le u v => [u, v]
  | .fle a u | .lef u a => (List.finRange n).map a ++ [u]
  | .bot u | .top u => [u]

/-- Literal satisfaction depends only on its occurring variables. -/
theorem holds_congr {V : Type*} (c : Fin n → Bool) (l : LitT n V)
    {ρ τ : V → DeciNSSE.Tree n} (h : ∀ v ∈ vars l, ρ v = τ v) :
    HoldsT c ρ l ↔ HoldsT c τ l := by
  cases l with
  | le u v =>
    simp only [vars, List.forall_mem_cons] at h
    simp_all [HoldsT]
  | fle a u =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | lef u a =>
    have hu := h u (by simp [vars])
    have ha : ρ ∘ a = τ ∘ a := by
      funext i
      exact h (a i) (by simp [vars])
    simp only [HoldsT, hu, ha]
  | bot u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]
  | top u => simp only [vars, List.forall_mem_cons] at h; simp_all [HoldsT]

end Pinning

/-- Finite bound pinning is a theorem, with no restriction
on the ambient variable carrier. Only the system and list of bounds are finite. -/
theorem finiteBoundPinning [NeZero n] {V : Type*} (χ : List (LitT n V)) : FiniteBoundPinning χ := by
  classical
  intro hf B hs
  let S : Finset V := (χ.flatMap Pinning.vars ++ B.map GroundBound.var).toFinset
  let W := Option {v // v ∈ S}
  let tag : V → W := fun v => if h : v ∈ S then some ⟨v, h⟩ else none
  let pull (ρ : V → DeciNSSE.Tree n) : W → DeciNSSE.Tree n := fun w =>
    match w with
    | none => DeciNSSE.Tree.bot
    | some v => ρ v.val
  have htag (ρ : V → DeciNSSE.Tree n) (v : V) (hv : v ∈ S) : pull ρ (tag v) = ρ v := by
    simp [pull, tag, hv]
  have hvar {l : LitT n V} (hl : l ∈ χ) {v : V} (hv : v ∈ Pinning.vars l) :
      v ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨l, hl, hv⟩)
  have hbvar {b : GroundBound n V} (hb : b ∈ B) : b.var ∈ S := by
    simp only [S, List.mem_toFinset, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨b, hb, rfl⟩)
  let χ' := χ.map (LitT.map tag)
  let B' : List (GroundBound n W) := B.map fun b => ⟨tag b.var, b.lower, b.tree⟩
  have hsat (ρ : V → DeciNSSE.Tree n) (hρ : SatT (fun _ => false) ρ χ) :
      SatT (fun _ => false) (pull ρ) χ' := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    rw [holdsT_map]
    exact (Pinning.holds_congr _ l0 (fun v hv => htag ρ v (hvar hl0 hv))).mpr (hρ l0 hl0)
  have hf' : SatisfiableTopIn FiniteTop χ' := by
    obtain ⟨ρ, hc, ht⟩ := hf
    refine ⟨pull ρ, ?_, hsat ρ ht⟩
    intro w
    cases w with
    | none => exact ⟨.bot, rfl⟩
    | some v => exact hc v.val
  obtain ⟨ρ, ht, hb⟩ := hs
  have hb' : ∀ b ∈ B', b.Holds (pull ρ) := by
    intro b hm
    obtain ⟨b0, hm0, rfl⟩ := List.mem_map.mp hm
    simpa only [GroundBound.Holds, htag ρ b0.var (hbvar hm0)] using hb b0 hm0
  obtain ⟨τ, hc, ht, hbτ⟩ := Pinning.finiteBoundPinning_fintype χ' hf' B'
    ⟨pull ρ, hsat ρ ht, hb'⟩
  refine ⟨τ ∘ tag, fun v => hc (tag v), ?_, ?_⟩
  · intro l hl
    exact (holdsT_map _ tag τ l).mp (ht _ (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · intro b hm
    exact hbτ ⟨tag b.var, b.lower, b.tree⟩ (List.mem_map.mpr ⟨b, hm, rfl⟩)

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
theorem sample_finite (n : ℕ) : SatisfiableTopIn FiniteTop (sample n) :=
  ⟨assignment (.node (fun _ => .bot)), assignment_finite _, assignment_sat _⟩

/-- Opposite bounds pin exactly the finite tree with top in the selected slot. -/
def bounds (i : Fin n) : List (GroundBound n ℕ) :=
  [⟨1, true, ACPins.lower [i] .top⟩, ⟨1, false, ACPins.lower [i] .top⟩]

/-- The example constraints and bounds have a common solution. -/
theorem sample_joint (i : Fin n) :
    ∃ ρ, SatT (fun _ => false) ρ (sample n) ∧ ∀ b ∈ bounds i, b.Holds ρ := by
  refine ⟨assignment (ACPins.lower [i] .top), assignment_sat _, ?_⟩
  simp [bounds, GroundBound.Holds, assignment]

/-- Both pinning premises have concrete witnesses; the carrier is ℕ. -/
theorem sample_realized [NeZero n] (i : Fin n) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ (sample n) ∧
      ∀ b ∈ bounds i, b.Holds τ :=
  finiteBoundPinning (sample n) (sample_finite n) (bounds i) (sample_joint i)

/-- The unary example satisfies the finite realization conclusion. -/
theorem unary_realized :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ (sample 1) ∧
      ∀ b ∈ bounds (0 : Fin 1), b.Holds τ := sample_realized 0

/-- The ternary example satisfies the finite realization conclusion. -/
theorem ternary_realized :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ (sample 3) ∧
      ∀ b ∈ bounds (2 : Fin 3), b.Holds τ := sample_realized 2

end PinningExamples


end DeciENSSE.Core.Full
