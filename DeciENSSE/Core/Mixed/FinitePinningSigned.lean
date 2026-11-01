import DeciENSSE.Core.Mixed.Leaf
import DeciENSSE.Support.TransferFin.FiniteMedian
import DeciENSSE.Support.Variance.Median
import DeciNSSE.Constraints.Signed
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Tree

/-! # Finite signed symmetrization

The finite median of a signed assignment, its dual, and a normalized finite
solution yields a finite assignment fixed by sign duality. The third input is
a finite tree, which is essential for finite realization.

## Main declarations

- `FinitePinning.symmetrize`
- `FinitePinning.symmetrize_fixed`
- `FinitePinning.symmetrize_sat`
-/

namespace DeciENSSE.Core.Mixed.FinitePinning
open DeciNSSE DeciENSSE.Core.Full

variable {n : ℕ} {V : Type*}

/-- Two covariant literals, with contravariant children changing sign. -/
def signedLit (c : Fin n → Bool) : LitT n V → List (LitT n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .fle a u => [.fle (fun i => (a i, c i)) (u, false),
      .lef (u, true) (fun i => (a i, !(c i)))]
  | .lef u a => [.lef (u, false) (fun i => (a i, c i)),
      .fle (fun i => (a i, !(c i))) (u, true)]
  | .bot u => [.bot (u, false), .top (u, true)]
  | .top u => [.top (u, false), .bot (u, true)]

/-- Translate each flat literal into constraints on paired signed variables. -/
def signed (c : Fin n → Bool) (χ : List (LitT n V)) : List (LitT n (V × Bool)) :=
  χ.flatMap (signedLit c)

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

/-- Signed satisfaction is characterized by the original signed literal clauses. -/
@[simp] theorem sat_signed_iff (c : Fin n → Bool) (A : V × Bool → DeciNSSE.Tree n)
    (χ : List (LitT n V)) :
    SatT (fun _ => false) A (signed c χ) ↔
      ∀ l ∈ χ, SatT (fun _ => false) A (signedLit c l) := by
  constructor
  · intro h l hl m hm
    exact h m (List.mem_flatMap.mpr ⟨l, hl, hm⟩)
  · intro h m hm
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp hm
    exact h l hl m hm

/-- Normalization preserves and reflects satisfaction of one literal. -/
theorem holds_normalize_iff (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n) (l : LitT n V) :
    SatT (fun _ => false) (normalize c ρ) (signedLit c l) ↔ HoldsT c ρ l := by
  cases l <;> simp [signedLit, SatT, HoldsT, normalize, DeciNSSE.treeLe_iff_normalize,
    DeciNSSE.normalize_node, ← DeciNSSE.dual_node, Function.comp_def]

/-- Normalization preserves and reflects satisfaction of the constraint list. -/
theorem sat_normalize_iff (c : Fin n → Bool) (ρ : V → DeciNSSE.Tree n)
    (χ : List (LitT n V)) :
    SatT (fun _ => false) (normalize c ρ) (signed c χ) ↔ SatT c ρ χ := by
  rw [sat_signed_iff]
  simp_rw [holds_normalize_iff]
  rfl

/-- The signed constraint system is closed under sign duality. -/
theorem sat_signDual {c : Fin n → Bool} {A : V × Bool → DeciNSSE.Tree n}
    {χ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c χ)) :
    SatT (fun _ => false) (signDual A) (signed c χ) := by
  rw [sat_signed_iff] at h ⊢
  intro l hl
  have hh := h l hl
  cases l <;> simpa [signedLit, SatT, HoldsT, signDual, ← DeciNSSE.dual_node, Function.comp_def,
    and_comm] using hh

/-- Decoding a fixed signed solution yields a solution of the original constraints. -/
theorem sat_decode (c : Fin n → Bool) {A : V × Bool → DeciNSSE.Tree n}
    {χ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c χ))
    (hf : signDual A = A) : SatT c (decode c A) χ := by
  apply (sat_normalize_iff c _ χ).mp
  rwa [normalize_decode c hf]

/-- Median closure includes the variable inequalities of `LitT`. -/
theorem sat_median {A B D : V → DeciNSSE.Tree n} {χ : List (LitT n V)}
    (ha : SatT (fun _ => false) A χ) (hb : SatT (fun _ => false) B χ)
    (hd : SatT (fun _ => false) D χ) :
    SatT (fun _ => false) (fun v => Support.medN (A v) (B v) (D v)) χ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  have h₃ := hd l hl
  cases l with
  | le u v =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    exact Support.medN_mono h₁ h₂ h₃
  | fle a u =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    have hh := Support.medN_mono h₁ h₂ h₃
    simpa only [Support.medN_node, Function.comp_def] using hh
  | lef u a =>
    simp only [HoldsT, DeciNSSE.treeLe_false_iff_le] at *
    have hh := Support.medN_mono h₁ h₂ h₃
    simpa only [Support.medN_node, Function.comp_def] using hh
  | bot u =>
    change Support.medN (A u) (B u) (D u) = DeciNSSE.Tree.bot
    change A u = DeciNSSE.Tree.bot at h₁
    change B u = DeciNSSE.Tree.bot at h₂
    simp [h₁, h₂]
  | top u =>
    change Support.medN (A u) (B u) (D u) = DeciNSSE.Tree.top
    change A u = DeciNSSE.Tree.top at h₁
    change B u = DeciNSSE.Tree.top at h₂
    simp [h₁, h₂]

/-- A finite third input is essential: the all-constructor tree cannot be used. -/
def symmetrize (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) : FTree n :=
  Support.FinT.fmed (A z) (Support.FinT.finD (A (z.1, !z.2))) (FTree.normalize c z.2 (D z.1))

/-- Finite symmetrization presents the median of the three tree assignments. -/
@[simp] theorem symmetrize_toTree (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) :
    (symmetrize c A D z).toTree =
      Support.medN (A z).toTree (signDual (FTree.toTree ∘ A) z)
        (normalize c (FTree.toTree ∘ D) z) := by
  simp [symmetrize, signDual, normalize]

/-- Finite median symmetrization is fixed by sign duality. -/
theorem symmetrize_fixed (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) :
    signDual (FTree.toTree ∘ symmetrize c A D) =
      FTree.toTree ∘ symmetrize c A D := by
  funext ⟨v, s⟩
  simp only [signDual, Function.comp_apply, symmetrize_toTree, normalize,
    Support.d_medN, DeciNSSE.dual_involutive, Bool.not_not, DeciNSSE.normalize_not]
  rw [Support.medN_swap]

/-- Finite median symmetrization preserves satisfaction of the signed constraints. -/
theorem symmetrize_sat {c : Fin n → Bool} {A : V × Bool → FTree n}
    {D : V → FTree n} {χ : List (LitT n V)}
    (ha : SatT (fun _ => false) (FTree.toTree ∘ A) (signed c χ))
    (hd : SatT c (FTree.toTree ∘ D) χ) :
    SatT (fun _ => false) (FTree.toTree ∘ symmetrize c A D) (signed c χ) := by
  have hh := sat_median ha (sat_signDual ha) ((sat_normalize_iff c _ χ).mpr hd)
  simpa only [Function.comp_def, symmetrize_toTree] using hh


end DeciENSSE.Core.Mixed.FinitePinning
