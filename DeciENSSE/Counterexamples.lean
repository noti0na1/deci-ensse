import DeciENSSE.Bounds
import DeciENSSE.Certificate
import DeciENSSE.Terms

/-! # Short counterexample words

This module combines the counterexample words of `DeciENSSE.Certificate` with the bounds of
`DeciENSSE.Bounds`. Let `φ` be a flat system over the visible variables `X` and `ψ` a flat
system over `X ⊕ Z`, with `v = |X|` and `s = |X| + |Z|`, and let `D` be one of the three tree
classes. If both systems are `D`-satisfiable and the entailment `φ ⊨_D ∃ Z. ψ` fails, then:

- over `{⊥, f, ⊤}`, with any variance, `(φ, ψ)` has a counterexample word of length at most
  `E₃(10v + 12s + 15) ≤ E₃(22s + 15)` (`exists_short_counterexampleWord`), and every
  counterexample word gives at most two visible observations that hold in some
  `D`-solution of `φ` and in no assignment that extends to a solution of `ψ`
  (`CounterexampleWord.countermodels_in`);
- over `{⊥, f}`, with `f` covariant, the gadget pair `(φ♮, ψ♮)` of `DeciENSSE.TopFree` has a
  counterexample word of length at most `E₃(20v + 24s + 15) ≤ E₃(44s + 15)`
  (`exists_short_counterexampleWord_gadget`), and every counterexample word of the gadget
  pair gives a top-free `D`-solution of `φ` without a top-free `D`-extension to a solution of
  `ψ` (`CounterexampleWord.gadget_countermodels`).

These are the statements of the paper's `thm:as-main`(3) and (4). The bounds are those of
`DeciENSSE.Bounds.exists_short_failure`; the length of a counterexample word is
`CounterexampleWord.length`, which counts the separator of a hole word
(`CounterexampleWord.length_ofHole`). The `D`-satisfiability of both systems reduces the
failure in `D` to a failure over arbitrary trees (`CertificateTreeClass.existsEntailsTIn_iff`).

## Main declarations

- `CertificateTreeClass.termClosed`, `CertificateTreeClass.hasWitnesses`,
  `CertificateTreeClass.existsEntailsTIn_iff`: the three tree classes.
- `CounterexampleWord.exists_conditionI_iff`, `CounterexampleWord.exists_conditionU_iff`,
  `CounterexampleWord.exists_hole_iff`: the three kinds of `def:as-certificate`, with lengths.
- `CounterexampleWord.exists_short_conditionI`, `CounterexampleWord.exists_short_conditionU`:
  `prop:as-bounds`(1) and (2) as counterexample words.
- `CounterexampleWord.isEmpty`: without visible variables there is no counterexample word.
- `exists_short_counterexampleWord_of_not_existsEntailsT`, `exists_short_counterexampleWord`,
  `CounterexampleWord.countermodels_in`: `thm:as-main`(3).
- `TopFree.satisfiableIn_gadgetAnte`, `TopFree.satisfiableIn_gadgetCons`,
  `exists_short_counterexampleWord_gadget`, `CounterexampleWord.gadget_countermodels`:
  `thm:as-main`(4).
-/

namespace DeciENSSE
open DeciNSSE Core.Full Core.Mixed Bounds

variable {n : ℕ}

/-! ## The three tree classes -/

namespace CertificateTreeClass

/-- Each of the three tree classes contains `⊥` and `⊤` and is closed under the
constructor. -/
theorem termClosed : (D : CertificateTreeClass) → TermClosed (D.Holds (n := n))
  | .all => termClosed_all
  | .regular => termClosed_reg
  | .finite => termClosed_fin

/-- In each of the three tree classes, every top-free tree has a gadget witness. -/
theorem hasWitnesses : (D : CertificateTreeClass) → TopFree.HasWitnesses (D.Holds (n := n))
  | .all => TopFree.hasWitnesses_all
  | .regular => TopFree.hasWitnesses_reg
  | .finite => TopFree.hasWitnesses_fin

/-- A solution in a tree class is a solution. -/
theorem satisfiable {V : Type*} {D : CertificateTreeClass} {c : Fin n → Bool}
    {χ : List (LitT n V)} (h : SatisfiableIn D.Holds c χ) : ∃ ρ, SatT c ρ χ := by
  obtain ⟨ρ, -, hρ⟩ := h
  exact ⟨ρ, hρ⟩

/-- For systems that are satisfiable in the tree class `D`, entailment in `D` is entailment
over arbitrary trees. -/
theorem existsEntailsTIn_iff {X Z : Type*} [Fintype X] [Fintype Z] (D : CertificateTreeClass)
    {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}
    (hφ : SatisfiableIn D.Holds c φ) (hψ : SatisfiableIn D.Holds c ψ) :
    ExistsEntailsTIn D.Holds c φ ψ ↔ ExistsEntailsT c φ ψ := by
  cases D with
  | all => exact Iff.rfl
  | regular => exact (existsEntailsTReg_iff c φ ψ).symm.trans (existsEntailsTReg_iff_mixed c φ ψ)
  | finite =>
    refine (existsEntailsTFin_iff c φ ψ).symm.trans ((existsEntailsTFin_iff_mixed c φ ψ).trans ?_)
    exact ⟨fun h => (h.resolve_left (not_not.mpr hφ)).2, fun h => Or.inr ⟨hψ, h⟩⟩

end CertificateTreeClass

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {c : Fin n → Bool} {φ : List (LitT n X)} {ψ : List (LitT n (X ⊕ Z))}

/-! ## The three kinds of counterexample words -/

namespace CounterexampleWord

@[simp] theorem length_ofI (q : X × Bool) (w : List (Fin n))
    (hf : (Sum.inl q.1, q.2, w) ∈ Mu c ψ) (hn : (q.1, q.2, w) ∉ Mu c φ) :
    (ofI q w hf hn).length = w.length := rfl

@[simp] theorem length_ofU (p : X × Bool) (w : List (Fin n)) (hl : Live c φ (p.1, p.2, w))
    (hd : DeadU c ψ p w) : (ofU p w hl hd).length = w.length := rfl

/-- A hole word `u♯t` has length `|u| + |t| + 1`. -/
@[simp] theorem length_ofHole (p q : X × Bool) (u t : List (Fin n)) (hU : CondU c φ ψ)
    (hh : (extractSelf c φ ψ p q).IsHole u t) :
    (ofHole p q u t hU hh).length = u.length + t.length + 1 := rfl

/-- The seed set of an (I0)-word is empty, so its hull is `μ_φ`. -/
@[simp] theorem hull_ofI (q : X × Bool) (w : List (Fin n))
    (hf : (Sum.inl q.1, q.2, w) ∈ Mu c ψ) (hn : (q.1, q.2, w) ∉ Mu c φ) :
    Hull c φ (ofI q w hf hn).seeds = Mu c φ := rfl

/-- The hull of a (U)-word `w` with `p` is `Cl_φ(p, w)`. -/
@[simp] theorem hull_ofU (p : X × Bool) (w : List (Fin n)) (hl : Live c φ (p.1, p.2, w))
    (hd : DeadU c ψ p w) : Hull c φ (ofU p w hl hd).seeds = Cl c φ (p.1, p.2, w) := rfl

/-- The hull of a hole word `u♯t` of `I_pq` is `Cl_φ(p, t)`. -/
@[simp] theorem hull_ofHole (p q : X × Bool) (u t : List (Fin n)) (hU : CondU c φ ψ)
    (hh : (extractSelf c φ ψ p q).IsHole u t) :
    Hull c φ (ofHole p q u t hU hh).seeds = Cl c φ (p.1, p.2, t) := rfl

/-- **(I0)-words** (`def:as-certificate`(1)): an (I0)-word of length `L` is a word `w` of
length `L` with `(q, w) ∈ μ_ψ` and `(q, w) ∉ μ_φ` for some `q ∈ X^±`. -/
theorem exists_conditionI_iff (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .conditionI, w.length = L) ↔
      ∃ q : X × Bool, ∃ w : List (Fin n), w.length = L ∧
        (Sum.inl q.1, q.2, w) ∈ Mu c ψ ∧ (q.1, q.2, w) ∉ Mu c φ := by
  constructor
  · rintro ⟨w, rfl⟩
    cases w with
    | ofI q w hf hn => exact ⟨q, w, rfl, hf, hn⟩
  · rintro ⟨q, w, rfl, hf, hn⟩
    exact ⟨.ofI q w hf hn, rfl⟩

/-- **(U)-words** (`def:as-certificate`(2)): a (U)-word of length `L` is a word `w` of length
`L` such that `(p, w)` is live in `φ` and `DeadU_ψ(p, w)` holds, for some `p ∈ X^±`. -/
theorem exists_conditionU_iff (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .conditionU, w.length = L) ↔
      ∃ p : X × Bool, ∃ w : List (Fin n), w.length = L ∧
        Live c φ (p.1, p.2, w) ∧ DeadU c ψ p w := by
  constructor
  · rintro ⟨w, rfl⟩
    cases w with
    | ofU p w hl hd => exact ⟨p, w, rfl, hl, hd⟩
  · rintro ⟨p, w, rfl, hl, hd⟩
    exact ⟨.ofU p w hl hd, rfl⟩

/-- **Hole words** (`def:as-certificate`(3)): hole words are used only when (U) holds, and a
hole word of length `L` is the separator word `u♯t`, of length `|u| + |t| + 1 = L`, of a hole
`(u, t)` of an extracted instance `I_pq` with `p, q ∈ X^±`. -/
theorem exists_hole_iff (L : ℕ) :
    (∃ w : CounterexampleWord c φ ψ .hole, w.length = L) ↔
      CondU c φ ψ ∧ ∃ p q : X × Bool, ∃ u t : List (Fin n),
        u.length + t.length + 1 = L ∧ (extractSelf c φ ψ p q).IsHole u t := by
  constructor
  · rintro ⟨w, rfl⟩
    cases w with
    | ofHole p q u t hU hh => exact ⟨hU, p, q, u, t, rfl, hh⟩
  · rintro ⟨hU, p, q, u, t, rfl, hh⟩
    exact ⟨.ofHole p q u t hU hh, rfl⟩

/-- A counterexample word names a visible variable. -/
theorem nonempty_var {k : CertificateKind} (w : CounterexampleWord c φ ψ k) : Nonempty X := by
  cases w with
  | ofI q => exact ⟨q.1⟩
  | ofU p => exact ⟨p.1⟩
  | ofHole p => exact ⟨p.1⟩

/-- Without visible variables there is no counterexample word (`prop:as-bounds`, `v = 0`). -/
theorem isEmpty [IsEmpty X] {k : CertificateKind} : IsEmpty (CounterexampleWord c φ ψ k) :=
  ⟨fun w => isEmptyElim (Classical.choice w.nonempty_var)⟩

/-- **(I0)-words** (`prop:as-bounds`(1)): if (I0) fails, there is an (I0)-word of length less
than `2^(2v+2s+2)`. No satisfiability hypothesis is needed. -/
theorem exists_short_conditionI (h : ¬ CondI0 c φ ψ) :
    ∃ w : CounterexampleWord c φ ψ .conditionI,
      w.length < 2 ^ (2 * Fintype.card X + 2 * (Fintype.card X + Fintype.card Z) + 2) := by
  obtain ⟨q, u, hu, hf, hn⟩ := (not_condI0_iff_short c φ ψ).mp h
  exact ⟨.ofI q u hf hn, hu⟩

/-- **(U)-words** (`prop:as-bounds`(2)): for satisfiable `φ`, if (U) fails, there is a
(U)-word of length at most `holeBound(N_U, d_{N_U}) ≤ E₃(10v + 10s + 17)`, where `N_U` is the
number of states of the unit reader. -/
theorem exists_short_conditionU (hφ : ∃ ρ, SatT c ρ φ) (h : ¬ CondU c φ ψ) :
    (∃ w : CounterexampleWord c φ ψ .conditionU,
      w.length ≤ DeciNSSE.RejectedTail.holeLengthBound (Fintype.card (TargetState X Z))) ∧
      DeciNSSE.RejectedTail.holeLengthBound (Fintype.card (TargetState X Z)) ≤
        E3 (10 * Fintype.card X + 10 * (Fintype.card X + Fintype.card Z) + 17) := by
  obtain ⟨⟨p, u, hu, hl, hd⟩, hb⟩ := exists_short_condU_word c φ ψ hφ h
  exact ⟨⟨.ofU p u hl hd, hu⟩, hb⟩

end CounterexampleWord

/-! ## The signature `{⊥, f, ⊤}`: `thm:as-main`(3) -/

/-- **Short counterexample words over arbitrary trees.** If `φ` and `ψ` are satisfiable and
`φ ⊭ ∃ Z. ψ`, then `(φ, ψ)` has a counterexample word of length at most
`E₃(10v + 12s + 15)`. -/
theorem exists_short_counterexampleWord_of_not_existsEntailsT (hφ : ∃ ρ, SatT c ρ φ)
    (hψ : ∃ ρ, SatT c ρ ψ) (h : ¬ ExistsEntailsT c φ ψ) :
    ∃ k, ∃ w : CounterexampleWord c φ ψ k,
      w.length ≤ E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) := by
  obtain ⟨-, ⟨p, w, hw, hf, hn⟩ | ⟨p, w, hw, hl, hd⟩ | ⟨-, hU, p, q, u, t, hh, hb⟩⟩ :=
    exists_short_failure c φ ψ hφ hψ h
  · exact ⟨_, .ofI p w hf hn, hw⟩
  · exact ⟨_, .ofU p w hl hd, hw⟩
  · exact ⟨_, .ofHole p q u t hU hh, hb⟩

/-- **Short counterexample words** (`thm:as-main`(3), first claim). Let `D` be one of the three
tree classes. If `φ` and `ψ` are `D`-satisfiable and `φ ⊭_D ∃ Z. ψ`, then `(φ, ψ)` has a
counterexample word of length at most `E₃(10v + 12s + 15) ≤ E₃(22s + 15)`. The bound depends
neither on the arity nor on the variance. -/
theorem exists_short_counterexampleWord (D : CertificateTreeClass)
    (hφ : SatisfiableIn D.Holds c φ) (hψ : SatisfiableIn D.Holds c ψ)
    (h : ¬ ExistsEntailsTIn D.Holds c φ ψ) :
    (∃ k, ∃ w : CounterexampleWord c φ ψ k,
      w.length ≤ E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      E3 (10 * Fintype.card X + 12 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (22 * (Fintype.card X + Fintype.card Z) + 15) :=
  ⟨exists_short_counterexampleWord_of_not_existsEntailsT
      (CertificateTreeClass.satisfiable hφ) (CertificateTreeClass.satisfiable hψ)
      fun he => h ((D.existsEntailsTIn_iff hφ hψ).mpr he),
    E3_le_E3 (by omega)⟩

/-- **Counterexample words determine countermodels** (`thm:as-main`(3), second claim). Let `D`
be a tree class in which `φ` is satisfiable. Every counterexample word determines at most two
visible observations such that `φ` has a solution with values in `D` in which they hold, and
no assignment in which they hold extends to a solution of `ψ`; in particular no such
`D`-solution has an extension with values in `D`. -/
theorem CounterexampleWord.countermodels_in {k : CertificateKind}
    (w : CounterexampleWord c φ ψ k) (D : CertificateTreeClass)
    (hφ : SatisfiableIn D.Holds c φ) :
    w.observations.length ≤ 2 ∧
      (∃ ρ, (∀ x, D.Holds (ρ x)) ∧ SatT c ρ φ ∧ ∀ o ∈ w.observations, o.Holds c ρ) ∧
      ∀ ρ, (∀ o ∈ w.observations, o.Holds c ρ) → ¬ ∃ σ, SatT c (Sum.elim ρ σ) ψ := by
  obtain ⟨⟨ρ, hD, hs, hb⟩, -⟩ := w.pinned_countermodels D hφ
  exact ⟨w.observations_length, ⟨ρ, hD, hs, (w.bounds_iff ρ).mp hb⟩,
    fun _ ho => w.observations_no_extension (CertificateTreeClass.satisfiable hφ) ho⟩

/-! ## The signature `{⊥, f}`: `thm:as-main`(4) -/

namespace TopFree

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- If `φ` has a top-free solution in a class with gadget witnesses, then `φ♮` has a solution
in the class. -/
theorem satisfiableIn_gadgetAnte {C : Tree n → Prop} (hC : HasWitnesses C) {xs : List X}
    (hxs : ∀ x, x ∈ xs) (φ : List (LitT n X))
    (h : SatisfiableIn (fun t => TopFree t ∧ C t) (fun _ => false) φ) :
    SatisfiableIn C (fun _ => false) (gadgetAnte xs φ) := by
  obtain ⟨ρ, hρ, hs⟩ := h
  choose y hyC hy using fun x => hC (ρ x) (hρ x).1 (hρ x).2
  refine ⟨Sum.elim ρ y, ?_, (satT_gadgetAnte hxs φ _).mpr ⟨hs, hy⟩⟩
  rintro (x | x)
  exacts [(hρ x).2, hyC x]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- If `ψ` has a top-free solution in a class with gadget witnesses, then `ψ♮` has a solution
in the class. -/
theorem satisfiableIn_gadgetCons {C : Tree n → Prop} (hC : HasWitnesses C) {zs : List Z}
    (hzs : ∀ z, z ∈ zs) (ψ : List (LitT n (X ⊕ Z)))
    (h : SatisfiableIn (fun t => TopFree t ∧ C t) (fun _ => false) ψ) :
    SatisfiableIn C (fun _ => false) (gadgetCons zs ψ) := by
  obtain ⟨τ, hτ, hs⟩ := h
  choose y hyC hy using fun v => hC (τ v) (hτ v).1 (hτ v).2
  refine ⟨Sum.elim (Sum.elim (τ ∘ .inl) (y ∘ .inl)) (Sum.elim (τ ∘ .inr) (y ∘ .inr)), ?_,
    (satT_gadgetCons hzs ψ _ _).mpr ⟨?_, fun z => hy (.inr z)⟩⟩
  · rintro ((x | x) | (z | z))
    exacts [(hτ _).2, hyC _, (hτ _).2, hyC _]
  · simpa only [Sum.elim_comp_inl, Sum.elim_comp_inl_inr] using hs

end TopFree

/-- **Short counterexample words over `{⊥, f}`** (`thm:as-main`(4), first claim). Let `f` be
covariant and `D` one of the three tree classes, and let `xs` and `zs` list the visible and the
hidden variables. If `φ` and `ψ` have top-free solutions in `D` and the entailment fails over
top-free trees of `D`, then the gadget pair `(φ♮, ψ♮)`, over `X ⊕ X` and `Z ⊕ Z`, has a
counterexample word of length at most `E₃(20v + 24s + 15) ≤ E₃(44s + 15)`. -/
theorem exists_short_counterexampleWord_gadget (D : CertificateTreeClass) {xs : List X}
    (hxs : ∀ x, x ∈ xs) {zs : List Z} (hzs : ∀ z, z ∈ zs)
    (hφ : SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ)
    (hψ : SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) ψ)
    (h : ¬ ExistsEntailsTIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ ψ) :
    (∃ k, ∃ w : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
        (TopFree.gadgetCons zs ψ) k,
      w.length ≤ E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15)) ∧
      E3 (20 * Fintype.card X + 24 * (Fintype.card X + Fintype.card Z) + 15) ≤
        E3 (44 * (Fintype.card X + Fintype.card Z) + 15) := by
  have hb := gadget_bound (X := X) (Z := Z)
  refine ⟨?_, hb.2⟩
  obtain ⟨⟨k, w, hw⟩, -⟩ := exists_short_counterexampleWord D
    (TopFree.satisfiableIn_gadgetAnte D.hasWitnesses hxs φ hφ)
    (TopFree.satisfiableIn_gadgetCons D.hasWitnesses hzs ψ hψ)
    fun he => h ((TopFree.existsEntailsTIn_iff_gadget D.hasWitnesses hxs hzs φ ψ).mpr he)
  exact ⟨k, w, hw.trans hb.1.le⟩

/-- **Counterexample words of the gadget pair determine countermodels over `{⊥, f}`**
(`thm:as-main`(4), second claim). Let `f` be covariant, `D` one of the three tree classes in
which `φ` has a top-free solution, and `xs` and `zs` lists of the visible and the hidden
variables. Every counterexample word of `(φ♮, ψ♮)` determines a top-free solution of `φ` in
`D` without a top-free extension in `D` to a solution of `ψ`: its observation pins have a
`D`-solution of `φ♮`, and every such solution restricts to one. -/
theorem CounterexampleWord.gadget_countermodels {k : CertificateKind}
    {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z} (hzs : ∀ z, z ∈ zs)
    (w : CounterexampleWord (fun _ => false) (TopFree.gadgetAnte xs φ)
      (TopFree.gadgetCons zs ψ) k) (D : CertificateTreeClass)
    (hφ : SatisfiableIn (fun t => TopFree t ∧ D.Holds t) (fun _ => false) φ) :
    (∃ ρ : X → Tree n, (∀ x, TopFree (ρ x) ∧ D.Holds (ρ x)) ∧ SatT (fun _ => false) ρ φ ∧
      ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
        SatT (fun _ => false) (Sum.elim ρ σ) ψ) ∧
      ∀ ρ : X ⊕ X → Tree n, (∀ x, D.Holds (ρ x)) →
        SatT (fun _ => false) ρ (TopFree.gadgetAnte xs φ) →
        (∀ b ∈ w.bounds, b.Holds (fun _ => false) ρ) →
        (∀ x, TopFree (ρ (.inl x)) ∧ D.Holds (ρ (.inl x))) ∧
          SatT (fun _ => false) (ρ ∘ Sum.inl) φ ∧
          ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
            SatT (fun _ => false) (Sum.elim (ρ ∘ Sum.inl) σ) ψ := by
  have hp := w.pinned_countermodels D (TopFree.satisfiableIn_gadgetAnte D.hasWitnesses hxs φ hφ)
  have hr : ∀ ρ : X ⊕ X → Tree n, (∀ x, D.Holds (ρ x)) →
      SatT (fun _ => false) ρ (TopFree.gadgetAnte xs φ) →
      (∀ b ∈ w.bounds, b.Holds (fun _ => false) ρ) →
      (∀ x, TopFree (ρ (.inl x)) ∧ D.Holds (ρ (.inl x))) ∧
        SatT (fun _ => false) (ρ ∘ Sum.inl) φ ∧
        ¬ ∃ σ, (∀ z, TopFree (σ z) ∧ D.Holds (σ z)) ∧
          SatT (fun _ => false) (Sum.elim (ρ ∘ Sum.inl) σ) ψ := fun ρ hD hs hb =>
    gadget_countermodel D.hasWitnesses hxs hzs φ ψ ρ hD hs
      fun ⟨σ, _, hσ⟩ => hp.2 ρ hD hs hb ⟨σ, hσ⟩
  obtain ⟨ρ, hD, hs, hb⟩ := hp.1
  obtain ⟨h₁, h₂, h₃⟩ := hr ρ hD hs hb
  exact ⟨⟨ρ ∘ Sum.inl, h₁, h₂, h₃⟩, hr⟩

end DeciENSSE
