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
    {A : V × Bool → FTree n} (D : V → FTree n)
    (h : ∀ p ∈ pins c B, p.Holds (fun _ => false) (FTree.toTree ∘ A)) :
    ∀ p ∈ pins c B, p.Holds (fun _ => false) (FTree.toTree ∘ symmetrize c A D) := by
  intro p hp
  have hh := bound_median (D := normalize c (FTree.toTree ∘ D)) p
    (h p hp) (pins_signDual h p hp)
  simpa only [Function.comp_def, symmetrize_toTree] using hh

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
  classical
  obtain ⟨δ, hδfin, hδ⟩ := hf
  choose D hD using hδfin
  have hDeq : FTree.toTree ∘ D = δ := funext hD
  have hf' : SatisfiableIn FiniteTop (fun _ => false) (Full.signed c χ) := by
    refine ⟨FinitePinning.normalize c δ, ?_,
      (FinitePinning.sat_normalize_iff c δ χ).mpr hδ⟩
    intro z
    exact ⟨FTree.normalize c z.2 (D z.1), by simp [FinitePinning.normalize, hD]⟩
  obtain ⟨ρ, hρ, hB⟩ := hs
  obtain ⟨β, hβfin, hβ, hβB⟩ := Full.finiteBoundPinning
    (Full.signed c χ) hf' (FinitePinning.pins c B)
    ⟨FinitePinning.normalize c ρ, (FinitePinning.sat_normalize_iff c ρ χ).mpr hρ,
      (FinitePinning.pins_normalize_iff c B ρ).mpr hB⟩
  choose A hA using hβfin
  have hAeq : FTree.toTree ∘ A = β := funext hA
  have hAsat : SatT (fun _ => false) (FTree.toTree ∘ A)
      (Full.signed c χ) := hAeq.symm ▸ hβ
  have hApins : ∀ p ∈ FinitePinning.pins c B, p.Holds (fun _ => false) (FTree.toTree ∘ A) :=
    hAeq.symm ▸ hβB
  let M := FinitePinning.symmetrize c A D
  have hfixed := FinitePinning.symmetrize_fixed c A D
  refine ⟨FinitePinning.decode c (FTree.toTree ∘ M), ?_, ?_, ?_⟩
  · intro v
    exact ⟨FTree.normalize c false (M (v, false)), by simp [FinitePinning.decode]⟩
  · exact FinitePinning.sat_decode c
      (FinitePinning.symmetrize_sat hAsat (hDeq.symm ▸ hδ)) hfixed
  · exact FinitePinning.pins_decode hfixed (FinitePinning.symmetrize_pins D hApins)

end DeciENSSE.Core.Mixed
