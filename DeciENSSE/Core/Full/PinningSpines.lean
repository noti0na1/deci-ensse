import DeciENSSE.Support.Transfer.RankedExtension
import DeciENSSE.Support.Transfer.Spines
import DeciENSSE.Support.TransferFin.CycleTransfer
import DeciNSSE.Constraints.Basic
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Tree
import DeciNSSE.Transfer.RankedExtension

/-! # Finite realization of path pins

Each path pin adds a ranked source or sink block. Cycle reflection preserves
finite satisfiability while induction retains an arbitrary finite list of pins.

## Main declarations

- `Pinning.PathPin`
- `Pinning.PathPin.extension`
- `Pinning.realize_pins`
-/

namespace DeciENSSE.Core.Full.Pinning
open DeciNSSE

variable {n : ℕ}

/-- The four assertions of equality or inequality with an extreme leaf. -/
inductive PinKind where
  | noBot | bot | top | noTop
  deriving DecidableEq

/-- Interpret an extreme-leaf assertion. -/
def PinKind.Holds (q : PinKind) (t : DeciNSSE.Tree n) : Prop :=
  match q with
  | .noBot => t ≠ DeciNSSE.Tree.bot
  | .bot => t = DeciNSSE.Tree.bot
  | .top => t = DeciNSSE.Tree.top
  | .noTop => t ≠ DeciNSSE.Tree.top

/-- An extreme-leaf assertion at a variable and path. -/
structure PathPin (n : ℕ) (V : Type*) where
  var : V
  word : List (Fin n)
  kind : PinKind

/-- Interpret a pin on the leaf-freezing trace of an assignment. -/
def PathPin.Holds {V : Type*} (p : PathPin n V) (ρ : V → DeciNSSE.Tree n) : Prop :=
  p.kind.Holds (Safety.trace (ρ p.var) p.word)

/-- Rename the variable of a path pin. -/
def PathPin.map {V W : Type*} (f : V → W) (p : PathPin n V) : PathPin n W :=
  ⟨f p.var, p.word, p.kind⟩

/-- Renaming a pin is equivalent to restricting the assignment. -/
@[simp] theorem PathPin.holds_map {V W : Type*} (f : V → W)
    (p : PathPin n V) (ρ : W → DeciNSSE.Tree n) :
    (p.map f).Holds ρ ↔ p.Holds (ρ ∘ f) := Iff.rfl

/-- Encode a path pin with fresh spine variables. -/
def PathPin.chain {k : ℕ} (p : PathPin n (Fin k)) :
    Constraint n (k + (2 * p.word.length + 2)) :=
  match p.kind with
  | .noBot => Support.noBotChainN p.var p.word
  | .bot => Support.botChainN p.var p.word
  | .top => Support.topChainN p.var p.word
  | .noTop => Support.noTopChainN p.var p.word

/-- Adding one path pin satisfies the ranked extension contract. -/
theorem PathPin.extension {k : ℕ} (χ : Constraint n k) (p : PathPin n (Fin k)) :
    Support.Ranked.ExtensionN χ (Support.ConstraintN.lift χ _ ++ p.chain)
      (Support.Spines.Source k p.word.length) (Support.Spines.Sink k p.word.length) Fin.val := by
  apply Support.Spines.extension_of_append
  · intro a c h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact Support.Spines.noBotChainN_fLe h
      | bot => exact (Support.Spines.fLe_not_mem_botChainN _ _ _ _ h).elim
      | top => exact Support.Spines.topChainN_fLe h
      | noTop => exact (Support.Spines.fLe_not_mem_noTopChainN _ _ _ _ h).elim
  · intro c b h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact (Support.Spines.leF_not_mem_noBotChainN _ _ _ _ h).elim
      | bot => exact Support.Spines.botChainN_leF h
      | top => exact (Support.Spines.leF_not_mem_topChainN _ _ _ _ h).elim
      | noTop => exact Support.Spines.noTopChainN_leF h

/-- A solution of the spine encoding satisfies the original pin. -/
theorem PathPin.chain_sound {k : ℕ} (p : PathPin n (Fin k))
    {ρ : Fin (k + (2 * p.word.length + 2)) → DeciNSSE.Tree n}
    (h : Covariant.Sat ρ p.chain) : p.Holds (ρ ∘ Fin.castAdd _) := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Support.Spines.noBotChainN_sound h
    | bot => exact Support.Spines.botChainN_sound h
    | top => exact Support.Spines.topChainN_sound h
    | noTop => exact Support.Spines.noTopChainN_sound h

/-- A valuation satisfying a pin extends to its spine encoding. -/
theorem PathPin.chain_extend {k : ℕ} (p : PathPin n (Fin k))
    (ρ : Fin k → DeciNSSE.Tree n) (h : p.Holds ρ) :
    Covariant.Sat (Support.Spines.extend ρ p.var p.var p.word) p.chain := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Support.Spines.noBotChainN_extend _ _ _ _ h
    | bot => exact Support.Spines.botChainN_extend _ _ _ _ h
    | top => exact Support.Spines.topChainN_extend _ _ _ _ h
    | noTop => exact Support.Spines.noTopChainN_extend _ _ _ _ h

/-- Add one ranked block at a time. Satisfiability of all remaining pins is
retained as a witness; finite satisfiability of the enlarged base follows
from cycle reflection and the finite-satisfiability criterion. -/
theorem realize_pins {k : ℕ} (O : List (PathPin n (Fin k))) (χ : Constraint n k)
    (hf : ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ)
    (hs : ∃ ρ, Covariant.Sat ρ χ ∧ ∀ p ∈ O, p.Holds ρ) :
    ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) χ ∧
      ∀ p ∈ O, p.Holds (FTree.toTree ∘ σ) := by
  cases O with
  | nil => obtain ⟨σ, hσ⟩ := hf; exact ⟨σ, hσ, by simp⟩
  | cons p O =>
    obtain ⟨ρ, hχ, hp⟩ := hs
    let ρ' := Support.Spines.extend ρ p.var p.var p.word
    have hr : ρ' ∘ Fin.castAdd _ = ρ := Support.Spines.extend_restrict ..
    have hs' : Covariant.Sat ρ' (Support.ConstraintN.lift χ _ ++ p.chain) :=
      (Covariant.sat_append ..).mpr ⟨(DeciNSSE.sat_rename ..).mpr (hr.symm ▸ hχ),
        p.chain_extend ρ (hp p (by simp))⟩
    have hf' := (Support.FinT.extension_satFin_iff (p.extension χ)).mpr ⟨⟨ρ', hs'⟩, hf⟩
    obtain ⟨σ, hσ, hO⟩ := realize_pins (O.map (PathPin.map (Fin.castAdd _)))
      (Support.ConstraintN.lift χ _ ++ p.chain) hf' ⟨ρ', hs', by
        simp only [List.forall_mem_map, PathPin.holds_map, hr]
        intro q hq; exact hp q (by simp [hq])⟩
    obtain ⟨hbase, hchain⟩ := (Covariant.sat_append ..).mp hσ
    refine ⟨σ ∘ Fin.castAdd _, (DeciNSSE.sat_rename ..).mp hbase, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact PathPin.chain_sound _ hchain
    · exact hO (q.map (Fin.castAdd _)) (List.mem_map.mpr ⟨q, hq, rfl⟩)

termination_by O.length

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

/-- The unary example satisfies the finite realization conclusion. -/
theorem unary_realized :
    ∃ σ : Fin 2 → FTree 1, Covariant.Sat (FTree.toTree ∘ σ) [.eqTop 1] ∧
      ∀ p ∈ pins (0 : Fin 1), p.Holds (FTree.toTree ∘ σ) := sample_realized 0

/-- The ternary example satisfies the finite realization conclusion. -/
theorem ternary_realized :
    ∃ σ : Fin 2 → FTree 3, Covariant.Sat (FTree.toTree ∘ σ) [.eqTop 1] ∧
      ∀ p ∈ pins (2 : Fin 3), p.Holds (FTree.toTree ∘ σ) := sample_realized 2

end SpineExamples


end DeciENSSE.Core.Full.Pinning
