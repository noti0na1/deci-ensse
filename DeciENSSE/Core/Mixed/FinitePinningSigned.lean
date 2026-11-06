import DeciENSSE.Core.Full.Classes
import DeciENSSE.Core.Full.Signed
import DeciENSSE.Core.Mixed.Leaf
import DeciENSSE.Support.Median
import DeciNSSE.Constraints.Signed
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Tree

/-! # Finite signed symmetrization

The median of a signed assignment, its dual, and a normalized solution is an
assignment fixed by sign duality. It is finite when the three inputs are
(`lem:tc-median`(3)); a finite third input is essential for this.

## Main declarations

- `FinitePinning.symmetrize`
- `FinitePinning.symmetrize_fixed`
- `FinitePinning.symmetrize_sat`
- `FinitePinning.symmetrize_finite`
- `FinitePinning.normalize_class_iff`, `FinitePinning.decode_class`: the signed
  correspondence preserves tree classes
-/

namespace DeciENSSE.Core.Mixed.FinitePinning
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*}

/-- Normalize each variable at both signs. -/
def normalize (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n) (z : V × Bool) : DeciNSSE.Tree n :=
  DeciNSSE.Tree.normalize c z.2 (ρ z.1)

/-- Swap the signs and dualize the corresponding tree values. -/
def signDual (A : V × Bool → DeciNSSE.Tree n) (z : V × Bool) : DeciNSSE.Tree n :=
  DeciNSSE.Tree.dual (A (z.1, !z.2))

/-- Recover an unsigned tree from the positively signed normalized value. -/
def decode (c : Fin n → Bool) (A : V × Bool → DeciNSSE.Tree n) (v : V) : DeciNSSE.Tree n :=
  DeciNSSE.Tree.normalize c false (A (v, false))

/-- Applying sign duality twice recovers the signed assignment. -/
@[simp] theorem signDual_involutive (A : V × Bool → DeciNSSE.Tree n) :
    signDual (signDual A) = A := by
  funext z
  simp [signDual]

/-- A normalized assignment is fixed by sign duality. -/
@[simp] theorem normalize_fixed (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n) :
    signDual (normalize c ρ) = normalize c ρ := by
  funext ⟨v, s⟩
  simp [normalize, signDual]

/-- Normalizing a decoded fixed assignment recovers the signed assignment. -/
theorem normalize_decode (c : Fin n → Bool) {A : V × Bool → DeciNSSE.Tree n}
    (h : signDual A = A) : normalize c (decode c A) = A := by
  funext ⟨v, s⟩
  cases s
  · simp [normalize, decode]
  · have hh := congrFun h (v, true)
    simpa [normalize, decode, signDual] using hh

/-- **Signed correspondence**, preservation of tree classes (`lem:bg-signed`):
`ρ ↦ ρ^±` preserves and reflects every class that normalization preserves and
reflects, among them `FiniteTop` and `RegularTop` (`Full.finiteTop_normalize_iff`,
`Full.regularTop_normalize_iff`). -/
theorem normalize_class_iff {c : Fin n → Bool} {C : DeciNSSE.Tree n → Prop}
    (hC : ∀ s t, C (DeciNSSE.Tree.normalize c s t) ↔ C t) (ρ : V → DeciNSSE.Tree n) :
    (∀ z, C (normalize c ρ z)) ↔ ∀ v, C (ρ v) :=
  ⟨fun h v => (hC false _).mp (h (v, false)), fun h z => (hC z.2 _).mpr (h z.1)⟩

/-- **Signed correspondence**, preservation of tree classes (`lem:bg-signed`): the
inverse map `decode` preserves every class that normalization preserves. -/
theorem decode_class {c : Fin n → Bool} {C : DeciNSSE.Tree n → Prop}
    (hC : ∀ s t, C (DeciNSSE.Tree.normalize c s t) ↔ C t) {A : V × Bool → DeciNSSE.Tree n}
    (hA : ∀ z, C (A z)) (v : V) : C (decode c A v) :=
  (hC false _).mpr (hA (v, false))

/-- Signed satisfaction is characterized by the original signed literal clauses. -/
@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : V × Bool → DeciNSSE.Tree n)
    (χ : List (LitT n V)) :
    SatT (fun _ => false) A (Full.signed c χ) ↔
      ∀ l ∈ χ, SatT (fun _ => false) A (Full.signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

/-- Normalization preserves and reflects satisfaction of one literal. -/
theorem holds_normalize_iff (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n) (l : LitT n V) :
    SatT (fun _ => false) (normalize c ρ) (Full.signedLit c l) ↔ HoldsT c ρ l := by
  cases l <;> simp [Full.signedLit, SatT, HoldsT, normalize, DeciNSSE.treeLe_iff_normalize,
    DeciNSSE.normalize_node, ← DeciNSSE.dual_node, Function.comp_def]

/-- Normalization preserves and reflects satisfaction of the constraint list. -/
theorem sat_normalize_iff (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n)
    (χ : List (LitT n V)) :
    SatT (fun _ => false) (normalize c ρ) (Full.signed c χ) ↔ SatT c ρ χ := by
  rw [sat_signed_iff]
  simp_rw [holds_normalize_iff]
  rfl

/-- The signed constraint system is closed under sign duality. -/
theorem sat_signDual {c : Fin n → Bool} {A : V × Bool → DeciNSSE.Tree n}
    {χ : List (LitT n V)} (h : SatT (fun _ => false) A (Full.signed c χ)) :
    SatT (fun _ => false) (signDual A) (Full.signed c χ) := by
  rw [sat_signed_iff] at h ⊢
  intro l hl
  have hh := h l hl
  cases l <;> simpa [Full.signedLit, SatT, HoldsT, signDual, ← DeciNSSE.dual_node,
    Function.comp_def,
    and_comm] using hh

/-- Decoding a fixed signed solution yields a solution of the original constraints. -/
theorem sat_decode (c : Fin n → Bool) {A : V × Bool → DeciNSSE.Tree n}
    {χ : List (LitT n V)} (h : SatT (fun _ => false) A (Full.signed c χ))
    (hf : signDual A = A) : SatT c (decode c A) χ := by
  apply (sat_normalize_iff c _ χ).mp
  rwa [normalize_decode c hf]

/-- Median closure includes the variable inequalities of `LitT`. -/
theorem sat_median {A B D : V → DeciNSSE.Tree n} {χ : List (LitT n V)}
    (ha : SatT (fun _ => false) A χ) (hb : SatT (fun _ => false) B χ)
    (hd : SatT (fun _ => false) D χ) :
    SatT (fun _ => false) (fun v => Support.Median.treeMedian (A v) (B v) (D v)) χ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  have h₃ := hd l hl
  cases l with
  | le u v =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    exact Support.Median.treeMedian_mono h₁ h₂ h₃
  | fle a u =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    have hh := Support.Median.treeMedian_mono h₁ h₂ h₃
    simpa only [Support.Median.treeMedian_node, Function.comp_def] using hh
  | lef u a =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    have hh := Support.Median.treeMedian_mono h₁ h₂ h₃
    simpa only [Support.Median.treeMedian_node, Function.comp_def] using hh
  | bot u =>
    change Support.Median.treeMedian (A u) (B u) (D u) = DeciNSSE.Tree.bot
    change A u = DeciNSSE.Tree.bot at h₁
    change B u = DeciNSSE.Tree.bot at h₂
    simp [h₁, h₂]
  | top u =>
    change Support.Median.treeMedian (A u) (B u) (D u) = DeciNSSE.Tree.top
    change A u = DeciNSSE.Tree.top at h₁
    change B u = DeciNSSE.Tree.top at h₂
    simp [h₁, h₂]

/-- The median of a signed assignment, its sign dual, and a normalized
assignment. -/
noncomputable def symmetrize (c : Fin n → Bool) (A : V × Bool → DeciNSSE.Tree n)
    (D : V → DeciNSSE.Tree n) (z : V × Bool) : DeciNSSE.Tree n :=
  Support.Median.treeMedian (A z) (signDual A z) (normalize c D z)

/-- Median symmetrization is fixed by sign duality. -/
theorem symmetrize_fixed (c : Fin n → Bool) (A : V × Bool → DeciNSSE.Tree n)
    (D : V → DeciNSSE.Tree n) : signDual (symmetrize c A D) = symmetrize c A D := by
  funext ⟨v, s⟩
  simp only [signDual, symmetrize, normalize, Support.Median.d_treeMedian,
    DeciNSSE.dual_involutive, Bool.not_not, DeciNSSE.normalize_not]
  rw [Support.Median.treeMedian_swap]

/-- Median symmetrization preserves satisfaction of the signed constraints. -/
theorem symmetrize_sat {c : Fin n → Bool} {A : V × Bool → DeciNSSE.Tree n}
    {D : V → DeciNSSE.Tree n} {χ : List (LitT n V)}
    (ha : SatT (fun _ => false) A (Full.signed c χ)) (hd : SatT c D χ) :
    SatT (fun _ => false) (symmetrize c A D) (Full.signed c χ) :=
  sat_median ha (sat_signDual ha) ((sat_normalize_iff c _ χ).mpr hd)

/-- Median symmetrization of finite assignments is finite (`lem:tc-median`(3)). -/
theorem symmetrize_finite (c : Fin n → Bool) {A : V × Bool → DeciNSSE.Tree n}
    {D : V → DeciNSSE.Tree n} (hA : ∀ z, Full.FiniteTop (A z))
    (hD : ∀ v, Full.FiniteTop (D v)) (z : V × Bool) :
    Full.FiniteTop (symmetrize c A D z) := by
  obtain ⟨a, ha⟩ := hA z
  obtain ⟨a', ha'⟩ := (Full.finiteTop_dual_iff _).mpr (hA (z.1, !z.2))
  obtain ⟨d, hd⟩ := (Full.finiteTop_normalize_iff c z.2 _).mpr (hD z.1)
  obtain ⟨m, hm⟩ := Support.Median.exists_ftree_treeMedian a a' d
  exact ⟨m, by rw [hm, ha, ha', hd]; rfl⟩

end DeciENSSE.Core.Mixed.FinitePinning
