import DeciENSSE.Support.Spines
import DeciNSSE.Transfer.RankedExtension
import DeciNSSE.Satisfiability.Finite

/-! # Ranked extensions with a fixed old block

The old variables embed through Fin.castAdd. Source and sink separation and
strictly increasing ranks reflect every nonempty cycle to the original system.

Cycle clashes are preserved and reflected by ranked extensions. A satisfiable
extension has a finite solution whenever its original system does.

## Main declarations

- `DeciNSSE.Ranked.Extension`: the shared rank contract.
- `Spines.extension_of_append`
- `RankedExtension.extension_cycleClash_iff`
- `RankedExtension.extension_satFin_iff`
-/

namespace DeciENSSE.Support.RankedExtension
open DeciENSSE.Support.Spines
open DeciNSSE

namespace Spines

variable {n k m : ℕ}

/-- The fresh lower block together with the bottom filler. -/
def Source (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  k ≤ z.val ∧ (z.val < k + L ∨ z.val = k + 2 * L)

/-- The fresh upper block together with the top filler. -/
def Sink (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  (k + L ≤ z.val ∧ z.val < k + 2 * L) ∨ z.val = k + 2 * L + 1

variable {L : ℕ}

/-- Every source lies outside the old block. -/
theorem source_not_old {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ z.val < k := by
  unfold Source at h; omega

/-- Every sink lies outside the old block. -/
theorem sink_not_old {z : V (k + (2 * L + 2))} (h : Sink k L z) : ¬ z.val < k := by
  unfold Sink at h; omega

/-- The source and sink classes are disjoint. -/
theorem source_not_sink {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ Sink k L z := by
  unfold Source at h; unfold Sink; omega

/-- Every variable is old, a source, or a sink. -/
theorem variable_cases (z : V (k + (2 * L + 2))) :
    (∃ u : V k, z = Fin.castAdd _ u) ∨ Source k L z ∨ Sink k L z := by
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val, h⟩, rfl⟩
  · right; unfold Source Sink; have := z.isLt; omega

/-- Each fresh lower-chain variable is a source. -/
theorem source_xv (x : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Source k L (xv x L j) := by
  simp only [Source, xv, dite_eq_left hj]; omega

/-- Each fresh upper-chain variable is a sink. -/
theorem sink_yv (y : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Sink k L (yv y L j) := by
  simp only [Sink, yv, dite_eq_left hj]; omega

/-- The bottom filler is a source. -/
theorem source_bv : Source k L (bv k L) := by simp [Source, bv]
/-- The top filler is a sink. -/
theorem sink_tv : Sink k L (tv k L) := by simp [Sink, tv]

/-- No lower-chain variable is a sink. -/
theorem not_sink_xv (x : V k) (j : ℕ) : ¬ Sink k L (xv x L j) := by
  unfold xv Sink
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

/-- No upper-chain variable is a source. -/
theorem not_source_yv (y : V k) (j : ℕ) : ¬ Source k L (yv y L j) := by
  unfold yv Source
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

/-- Indices strictly increase along the lower chain. -/
theorem xv_lt_next (x : V k) {j : ℕ} (hj : j < L) :
    (xv x L j).val < (xv x L (j + 1)).val := by
  unfold xv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

/-- Indices strictly increase along the upper chain. -/
theorem yv_lt_next (y : V k) {j : ℕ} (hj : j < L) :
    (yv y L j).val < (yv y L (j + 1)).val := by
  unfold yv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

/-- Every lower-chain index precedes the bottom filler. -/
theorem xv_lt_bv (x : V k) (j : ℕ) : (xv x L j).val < (bv k L).val := by
  unfold xv bv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

/-- Every upper-chain index precedes the top filler. -/
theorem yv_lt_tv (y : V k) (j : ℕ) : (yv y L j).val < (tv k L).val := by
  unfold yv tv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

/-! ## Literal classification for the chains -/

/-- A lower step: every child (the next spine variable or the bottom filler)
is a source of strictly greater index. -/
theorem lowerSteps_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ lowerSteps (xv x ν.length) (bv k ν.length) ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_lowerSteps_iff.mp h
  simp only [lowerLink, Lit.fLe.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_sink_xv _ _⟩
  rcases spineChildren_eq_or ν[j] i (xv x ν.length (j + 1)) (bv k ν.length) with h | h <;>
    rw [h]
  · exact ⟨source_xv x ⟨by omega, by omega⟩, xv_lt_next x hj⟩
  · exact ⟨source_bv, xv_lt_bv x j⟩

/-- An upper step: every child (the next spine variable or the top filler)
is a sink of strictly greater index. -/
theorem upperSteps_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ upperSteps (yv y ν.length) (tv k ν.length) ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_upperSteps_iff.mp h
  simp only [upperLink, Lit.leF.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_source_yv _ _⟩
  rcases spineChildren_eq_or ν[j] i (yv y ν.length (j + 1)) (tv k ν.length) with h | h <;>
    rw [h]
  · exact ⟨sink_yv y ⟨by omega, by omega⟩, yv_lt_next y hj⟩
  · exact ⟨sink_tv, yv_lt_tv y j⟩

/-- Every lower constructor literal in this chain satisfies the rank contract. -/
theorem noBotChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ noBotChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.fLe.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨source_bv, xv_lt_bv x _⟩, not_sink_xv _ _⟩

/-- Every lower constructor literal in this chain satisfies the rank contract. -/
theorem topChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ topChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp [reduceCtorEq] at h

/-- Every upper constructor literal in this chain satisfies the rank contract. -/
theorem noTopChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ noTopChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.leF.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨sink_tv, yv_lt_tv y _⟩, not_source_yv _ _⟩

/-- Every upper constructor literal in this chain satisfies the rank contract. -/
theorem botChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ botChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp [reduceCtorEq] at h

/-- This chain contains no lower constructor literal. -/
theorem fLe_not_mem_botChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ botChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

/-- This chain contains no lower constructor literal. -/
theorem fLe_not_mem_noTopChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ noTopChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

/-- This chain contains no upper constructor literal. -/
theorem leF_not_mem_noBotChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ noBotChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

/-- This chain contains no upper constructor literal. -/
theorem leF_not_mem_topChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ topChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

/-- Each original literal belongs to the lifted constraint after renaming. -/
theorem mem_lift_of_mem {ϕ : Constraint n k} {l : Lit n k} (hl : l ∈ ϕ) :
    l.rename (Fin.castAdd m) ∈ DeciENSSE.Support.Spines.Constraint.lift ϕ m :=
  List.mem_map.mpr ⟨l, hl, rfl⟩

/-- Any fresh block whose constructor literals are classified like the chain
literals extends the lifted constraint. -/
theorem extension_of_append {ϕ : Constraint n k} {A : Constraint n (k + (2 * L + 2))}
    (hlow : ∀ a c, Lit.fLe a c ∈ A →
      (∀ i, Source k L (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k L c)
    (hup : ∀ c b, Lit.leF c b ∈ A →
      (∀ i, Sink k L (b i) ∧ c.val < (b i).val) ∧ ¬ Source k L c) :
    DeciNSSE.Ranked.Extension (Fin.castAdd (2 * L + 2)) ϕ
      (DeciENSSE.Support.Spines.Constraint.lift ϕ _ ++ A)
      (Source k L) (Sink k L)
      Fin.val where
  injective := Fin.castAdd_injective _ _
  not_source_old := fun u h => source_not_old h u.isLt
  not_sink_old := fun u h => sink_not_old h u.isLt
  source_not_sink := source_not_sink
  variable_cases := variable_cases
  old_mem := fun l hl => List.mem_append_left _ (mem_lift_of_mem hl)
  lower := by
    intro a c h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (DeciNSSE.fLe_mem_rename h)
    · exact Or.inr (hlow a c h)
  upper := by
    intro c b h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (DeciNSSE.leF_mem_rename h)
    · exact Or.inr (hup c b h)

end Spines
end DeciENSSE.Support.RankedExtension

namespace DeciENSSE.Support.RankedExtension
open DeciNSSE

variable {n k m : ℕ}

section Extension

variable {ϕ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

/-- The old block of a solution of an extension solves the base system. -/
theorem extension_restrict_sat (e : DeciNSSE.Ranked.Extension (Fin.castAdd m) ϕ ψ Source Sink rank)
    {ρ' : V (k + m) → DeciNSSE.Tree n} (h : Covariant.Sat ρ' ψ) :
    Covariant.Sat (ρ' ∘ Fin.castAdd m) ϕ := by
  intro l hl
  exact (Lit.holds_rename _ _ _).mp (h _ (e.old_mem l hl))

/-- A ranked extension has a cycle clash exactly when its base has one. -/
theorem extension_cycleClash_iff
    (e : DeciNSSE.Ranked.Extension (Fin.castAdd m) ϕ ψ Source Sink rank) :
    DeciNSSE.CycleClash ψ ↔ DeciNSSE.CycleClash ϕ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.old_mem, hd.map _ e.old_mem, hu.map _ e.old_mem⟩

/-- A ranked extension is finitely satisfiable exactly when it is satisfiable and
its base is finitely satisfiable. -/
theorem extension_satFin_iff (e : DeciNSSE.Ranked.Extension (Fin.castAdd m) ϕ ψ Source Sink rank) :
    (∃ σ : V (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨_, hσ⟩, ⟨σ ∘ Fin.castAdd m, extension_restrict_sat e hσ⟩⟩
  · rintro ⟨⟨ρ', hρ'⟩, hf⟩
    apply DeciNSSE.satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ', hρ'⟩,
      fun hc => (DeciNSSE.satFin_iff.mp hf).2 ((extension_cycleClash_iff e).mp hc)⟩

end Extension

end DeciENSSE.Support.RankedExtension
