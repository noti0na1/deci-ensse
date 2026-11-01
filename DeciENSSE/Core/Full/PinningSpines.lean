import DeciENSSE.Support.RankedExtension
import DeciENSSE.Support.Spines
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
  | .noBot => Support.Spines.noBotChain p.var p.word
  | .bot => Support.Spines.botChain p.var p.word
  | .top => Support.Spines.topChain p.var p.word
  | .noTop => Support.Spines.noTopChain p.var p.word

/-- Adding one path pin satisfies the ranked extension contract. -/
theorem PathPin.extension {k : ℕ} (χ : Constraint n k) (p : PathPin n (Fin k)) :
    DeciNSSE.Ranked.Extension (Fin.castAdd _) χ (Support.Spines.Constraint.lift χ _ ++ p.chain)
      (Support.RankedExtension.Spines.Source k p.word.length)
      (Support.RankedExtension.Spines.Sink k p.word.length) Fin.val := by
  apply Support.RankedExtension.Spines.extension_of_append
  · intro a c h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact Support.RankedExtension.Spines.noBotChain_fLe h
      | bot => exact (Support.RankedExtension.Spines.fLe_not_mem_botChain _ _ _ _ h).elim
      | top => exact Support.RankedExtension.Spines.topChain_fLe h
      | noTop => exact (Support.RankedExtension.Spines.fLe_not_mem_noTopChain _ _ _ _ h).elim
  · intro c b h
    cases p with | mk v w q =>
      cases q with
      | noBot => exact (Support.RankedExtension.Spines.leF_not_mem_noBotChain _ _ _ _ h).elim
      | bot => exact Support.RankedExtension.Spines.botChain_leF h
      | top => exact (Support.RankedExtension.Spines.leF_not_mem_topChain _ _ _ _ h).elim
      | noTop => exact Support.RankedExtension.Spines.noTopChain_leF h

/-- A solution of the spine encoding satisfies the original pin. -/
theorem PathPin.chain_sound {k : ℕ} (p : PathPin n (Fin k))
    {ρ : Fin (k + (2 * p.word.length + 2)) → DeciNSSE.Tree n}
    (h : Covariant.Sat ρ p.chain) : p.Holds (ρ ∘ Fin.castAdd _) := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Support.Spines.noBotChain_sound h
    | bot => exact Support.Spines.botChain_sound h
    | top => exact Support.Spines.topChain_sound h
    | noTop => exact Support.Spines.noTopChain_sound h

/-- A valuation satisfying a pin extends to its spine encoding. -/
theorem PathPin.chain_extend {k : ℕ} (p : PathPin n (Fin k))
    (ρ : Fin k → DeciNSSE.Tree n) (h : p.Holds ρ) :
    Covariant.Sat (Support.Spines.extend ρ p.var p.var p.word) p.chain := by
  cases p with | mk v w q =>
    cases q with
    | noBot => exact Support.Spines.noBotChain_extend _ _ _ _ h
    | bot => exact Support.Spines.botChain_extend _ _ _ _ h
    | top => exact Support.Spines.topChain_extend _ _ _ _ h
    | noTop => exact Support.Spines.noTopChain_extend _ _ _ _ h

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
    have hs' : Covariant.Sat ρ' (Support.Spines.Constraint.lift χ _ ++ p.chain) :=
      (Covariant.sat_append ..).mpr ⟨(DeciNSSE.sat_rename ..).mpr (hr.symm ▸ hχ),
        p.chain_extend ρ (hp p (by simp))⟩
    have hf' := (Support.RankedExtension.extension_satFin_iff (p.extension χ)).mpr ⟨⟨ρ', hs'⟩, hf⟩
    obtain ⟨σ, hσ, hO⟩ := realize_pins (O.map (PathPin.map (Fin.castAdd _)))
      (Support.Spines.Constraint.lift χ _ ++ p.chain) hf' ⟨ρ', hs', by
        simp only [List.forall_mem_map, PathPin.holds_map, hr]
        intro q hq; exact hp q (by simp [hq])⟩
    obtain ⟨hbase, hchain⟩ := (Covariant.sat_append ..).mp hσ
    refine ⟨σ ∘ Fin.castAdd _, (DeciNSSE.sat_rename ..).mp hbase, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact PathPin.chain_sound _ hchain
    · exact hO (q.map (Fin.castAdd _)) (List.mem_map.mpr ⟨q, hq, rfl⟩)

termination_by O.length

end DeciENSSE.Core.Full.Pinning
