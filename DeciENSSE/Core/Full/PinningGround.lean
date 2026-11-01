import DeciENSSE.Core.Full.ACPins
import DeciENSSE.Core.Full.Classes
import DeciENSSE.Core.Full.Flatten
import DeciENSSE.Core.Full.PinningSpines
import DeciNSSE.Constraints.Basic
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Tree

/-! # Finite realization of ground bounds

Finite ground comparisons reduce to finitely many path pins. The resulting
finite solution preserves the flat constraints and every ground bound.

## Main declarations

- `Pinning.groundPins_iff`
- `Pinning.finiteBoundPinning_fintype`
-/

namespace DeciENSSE.Core.Full.Pinning
open DeciNSSE

variable {n : ℕ}

/-- Prefix a path pin by one child direction. -/
def PathPin.prefix {V : Type*} (i : Fin n) (p : PathPin n V) : PathPin n V :=
  ⟨p.var, i :: p.word, p.kind⟩

/-- A prefixed pin on a constructor is the original pin on the selected child. -/
@[simp] theorem PathPin.holds_prefix {V : Type*} (i : Fin n) (p : PathPin n V)
    (ρ : V → DeciNSSE.Tree n) :
    (p.prefix i).Holds ρ ↔ p.Holds (fun v => Safety.descend (ρ v) i) := Iff.rfl

/-- Encode a finite ground bound as finitely many extreme-leaf path pins. -/
def groundPins {V : Type*} (v : V) (lower : Bool) : FTree n → List (PathPin n V)
  | .bot => if lower then [] else [⟨v, [], .bot⟩]
  | .top => if lower then [⟨v, [], .top⟩] else []
  | .node a => ⟨v, [], if lower then .noBot else .noTop⟩ ::
      (List.finRange n).flatMap (fun i =>
        (groundPins v lower (a i)).map (PathPin.prefix i))

/-- A lower constructor comparison is determined by child traces and the root. -/
theorem node_le_descend (a : Fin n → DeciNSSE.Tree n) (t : DeciNSSE.Tree n) :
    DeciNSSE.Tree.node a ≤ t ↔ t ≠ DeciNSSE.Tree.bot ∧ ∀ i, a i ≤ Safety.descend t i := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩ <;>
    simp [DeciNSSE.Tree.node_le_node_iff]

/-- An upper constructor comparison is determined by child traces and the root. -/
theorem le_node_descend (t : DeciNSSE.Tree n) (a : Fin n → DeciNSSE.Tree n) :
    t ≤ DeciNSSE.Tree.node a ↔ t ≠ DeciNSSE.Tree.top ∧ ∀ i, Safety.descend t i ≤ a i := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩ <;>
    simp [DeciNSSE.Tree.node_le_node_iff]

/-- A ground comparison is a finite conjunction of the four path predicates.
Trace freezes at bottom and top, so the characterization also covers a leaf
of the compared variable above a node of the ground tree. -/
theorem groundPins_iff {V : Type*} (v : V) (lower : Bool) (g : FTree n)
    (ρ : V → DeciNSSE.Tree n) :
    (∀ p ∈ groundPins v lower g, p.Holds ρ) ↔
      if lower then g.toTree ≤ ρ v else ρ v ≤ g.toTree := by
  induction g generalizing ρ with
  | bot => cases lower <;> simp [groundPins, PathPin.Holds, PinKind.Holds]
  | top => cases lower <;> simp [groundPins, PathPin.Holds, PinKind.Holds]
  | node a ih =>
    simp only [groundPins, List.forall_mem_cons, List.forall_mem_flatMap,
      List.mem_finRange, forall_const,
      List.forall_mem_map, PathPin.holds_prefix, ih]
    cases lower <;>
      simp [PathPin.Holds, PinKind.Holds, le_node_descend, node_le_descend]

/-- Finite bound pinning holds for every finite variable type. -/
theorem finiteBoundPinning_fintype [NeZero n] {V : Type*} [Fintype V] (χ : List (LitT n V)) :
    FiniteBoundPinning χ := by
  classical
  intro hf B hs
  let e := Fintype.equivFin (Flatten.Vars V)
  let O := B.flatMap fun b => groundPins b.var b.lower b.tree
  have hO (ρ : V → DeciNSSE.Tree n) :
      (∀ p ∈ O, p.Holds ρ) ↔ ∀ b ∈ B, b.Holds (fun _ => false) ρ := by
    simp only [O, List.forall_mem_flatMap, groundPins_iff, GroundBound.Holds,
      DeciNSSE.treeLe_false_iff_le]
  obtain ⟨ρ, hχ, hb⟩ := hs
  obtain ⟨σ, hσ, hp⟩ := realize_pins
    (O.map (PathPin.map (fun v => e (.inl v)))) (Flatten.flatten (fun _ => false) e χ)
    (by simpa only [DeciNSSE.sat_false] using
      (Flatten.finite_iff (fun _ => false) e χ).mp hf)
    ⟨_, (by simpa only [DeciNSSE.sat_false] using Flatten.forward (fun _ => false) e hχ), by
      simp only [List.forall_mem_map, PathPin.holds_map]
      have he : (Flatten.extend (fun _ => false) ρ ∘ e.symm) ∘ (fun v => e (.inl v)) = ρ := by
        funext v; simp [Flatten.extend]
      rw [he]; exact (hO ρ).mpr hb⟩
  refine ⟨fun v => (σ (e (.inl v))).toTree, fun v => ⟨_, rfl⟩,
    Flatten.backward (fun _ => false) e (by simpa only [DeciNSSE.sat_false] using hσ), (hO _).mp ?_⟩
  intro p hm
  exact hp (p.map (fun v => e (.inl v))) (List.mem_map.mpr ⟨p, hm, rfl⟩)

end DeciENSSE.Core.Full.Pinning
