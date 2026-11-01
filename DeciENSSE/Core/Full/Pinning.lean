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
  have hf' : SatisfiableIn FiniteTop (fun _ => false) χ' := by
    obtain ⟨ρ, hc, ht⟩ := hf
    refine ⟨pull ρ, ?_, hsat ρ ht⟩
    intro w
    cases w with
    | none => exact ⟨.bot, rfl⟩
    | some v => exact hc v.val
  obtain ⟨ρ, ht, hb⟩ := hs
  have hb' : ∀ b ∈ B', b.Holds (fun _ => false) (pull ρ) := by
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

end DeciENSSE.Core.Full
