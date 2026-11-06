import DeciENSSE.Core.Full.Pinning
import DeciENSSE.Core.Mixed.FinitePinningSigned
import DeciENSSE.Support.Median
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Tree

/-! # Mixed finite bound pinning

Paired signed pins survive duality and median symmetrization. Decoding the
finite symmetric solution preserves every requested mixed ground bound.

## Main declarations

- `FinitePinning.pins`
- `FinitePinning.symmetrize_pins`
- `exists_finite_sat_groundBounds`
-/

namespace DeciENSSE.Core.Mixed
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ}

namespace FinitePinning
variable {V : Type*}

/-- A bound and its dual: the negative copy reverses the inequality. -/
def pin (c : Fin n → Bool) (b : GroundBound n V) (s : Bool) : GroundBound n (V × Bool) :=
  ⟨(b.var, s), Bool.xor b.lower s, FTree.normalize c s b.tree⟩

/-- Include both signed forms of every finite ground bound. -/
def pins (c : Fin n → Bool) (B : List (GroundBound n V)) : List (GroundBound n (V × Bool)) :=
  B.flatMap fun b => [pin c b false, pin c b true]

/-- A list of paired pins holds exactly when both signs of every bound hold. -/
theorem pins_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (A : V × Bool → DeciNSSE.Tree n) :
    (∀ p ∈ pins c B, p.Holds (fun _ => false) A) ↔
      ∀ b ∈ B, ∀ s, (pin c b s).Holds (fun _ => false) A := by
  constructor
  · intro h b hb s
    apply h
    apply List.mem_flatMap.mpr
    exact ⟨b, hb, by cases s <;> simp⟩
  · intro h p hp
    obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h b hb false
    · exact h b hb true

/-- A normalized signed pin is equivalent to its original mixed bound. -/
theorem pin_normalize_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (ρ : V → DeciNSSE.Tree n) :
    (pin c b s).Holds (fun _ => false) (normalize c ρ) ↔ b.Holds c ρ := by
  obtain ⟨v, lower, g⟩ := b
  cases lower <;> cases s <;>
    simp [pin, GroundBound.Holds, normalize, DeciNSSE.treeLe_iff_normalize]

/-- Normalization preserves and reflects every paired ground-bound pin. -/
theorem pins_normalize_iff (c : Fin n → Bool) (B : List (GroundBound n V))
    (ρ : V → DeciNSSE.Tree n) :
    (∀ p ∈ pins c B, p.Holds (fun _ => false) (normalize c ρ)) ↔ ∀ b ∈ B, b.Holds c ρ := by
  simp only [pins_iff, pin_normalize_iff, forall_const]

/-- Sign-duality exchanges the two bounds belonging to one original pin. -/
theorem pin_signDual_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (A : V × Bool → DeciNSSE.Tree n) :
    (pin c b s).Holds (fun _ => false) (signDual A) ↔ (pin c b (!s)).Holds (fun _ => false) A := by
  obtain ⟨v, lower, g⟩ := b
  cases lower <;> cases s <;>
    simp only [pin, GroundBound.Holds, DeciNSSE.treeLe_false_iff_le, FTree.normalize_toTree,
      signDual,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, DeciNSSE.normalize_true]
  all_goals exact (DeciNSSE.dual_le_iff _ _).symm.trans (by simp)

/-- The paired signed pins are preserved by sign duality. -/
theorem pins_signDual {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → DeciNSSE.Tree n} (h : ∀ p ∈ pins c B, p.Holds (fun _ => false) A) :
    ∀ p ∈ pins c B, p.Holds (fun _ => false) (signDual A) := by
  rw [pins_iff] at h ⊢
  intro b hb s
  exact (pin_signDual_iff c b s A).mpr (h b hb (!s))

/-- Two inputs satisfying a bound suffice, regardless of the third input. -/
theorem bound_median (b : GroundBound n V) {A A' D : V → DeciNSSE.Tree n}
    (ha : b.Holds (fun _ => false) A) (hb : b.Holds (fun _ => false) A') :
    b.Holds (fun _ => false) (fun v => Support.Median.treeMedian (A v) (A' v) (D v)) := by
  simp only [GroundBound.Holds, DeciNSSE.treeLe_false_iff_le] at ha hb ⊢
  obtain ⟨v, lower, g⟩ := b
  cases lower with
  | false =>
    change A v ≤ g.toTree at ha
    change A' v ≤ g.toTree at hb
    change Support.Median.treeMedian (A v) (A' v) (D v) ≤ g.toTree
    simpa using Support.Median.treeMedian_mono ha hb (le_refl (D v))
  | true =>
    change g.toTree ≤ A v at ha
    change g.toTree ≤ A' v at hb
    change g.toTree ≤ Support.Median.treeMedian (A v) (A' v) (D v)
    simpa using Support.Median.treeMedian_mono ha hb (le_refl (D v))

/-- Median symmetrization preserves every paired signed pin. -/
theorem symmetrize_pins {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → DeciNSSE.Tree n} (D : V → DeciNSSE.Tree n)
    (h : ∀ p ∈ pins c B, p.Holds (fun _ => false) A) :
    ∀ p ∈ pins c B, p.Holds (fun _ => false) (symmetrize c A D) := fun p hp =>
  bound_median (D := normalize c D) p (h p hp) (pins_signDual h p hp)

/-- Decoding a symmetric assignment satisfying the pins preserves the mixed bounds. -/
theorem pins_decode {c : Fin n → Bool} {B : List (GroundBound n V)}
    {A : V × Bool → DeciNSSE.Tree n} (hf : signDual A = A)
    (h : ∀ p ∈ pins c B, p.Holds (fun _ => false) A) : ∀ b ∈ B, b.Holds c (decode c A) := by
  apply (pins_normalize_iff c B _).mp
  rwa [normalize_decode c hf]

end FinitePinning

/-- Every consistent finite list of ground pins can be realized finitely,
provided the unpinned system has some finite solution. -/
theorem exists_finite_sat_groundBounds [NeZero n] {V : Type*} (c : Fin n → Bool)
    (χ : List (LitT n V))
    (hf : ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT c τ χ)
    (B : List (GroundBound n V))
    (hs : ∃ ρ, SatT c ρ χ ∧ ∀ b ∈ B, b.Holds c ρ) :
    ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT c τ χ ∧ ∀ b ∈ B, b.Holds c τ := by
  obtain ⟨δ, hδfin, hδ⟩ := hf
  have hf' : SatisfiableIn FiniteTop (fun _ => false) (Full.signed c χ) :=
    ⟨FinitePinning.normalize c δ,
      (FinitePinning.normalize_class_iff (finiteTop_normalize_iff c) δ).mpr hδfin,
      (FinitePinning.sat_normalize_iff c δ χ).mpr hδ⟩
  obtain ⟨ρ, hρ, hB⟩ := hs
  obtain ⟨β, hβfin, hβ, hβB⟩ := Full.finiteBoundPinning
    (Full.signed c χ) hf' (FinitePinning.pins c B)
    ⟨FinitePinning.normalize c ρ, (FinitePinning.sat_normalize_iff c ρ χ).mpr hρ,
      (FinitePinning.pins_normalize_iff c B ρ).mpr hB⟩
  have hfixed := FinitePinning.symmetrize_fixed c β δ
  refine ⟨FinitePinning.decode c (FinitePinning.symmetrize c β δ), ?_, ?_, ?_⟩
  · exact FinitePinning.decode_class (finiteTop_normalize_iff c)
      (FinitePinning.symmetrize_finite c hβfin hδfin)
  · exact FinitePinning.sat_decode c (FinitePinning.symmetrize_sat hβ hδ) hfixed
  · exact FinitePinning.pins_decode hfixed (FinitePinning.symmetrize_pins δ hβB)

end DeciENSSE.Core.Mixed
