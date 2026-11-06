import DeciENSSE.Subsumption

/-! # Examples of subsumption of constrained types

The worked examples of the section on constrained types, for arrow types: arity `2`, with
`f(a₀, a₁) = a₀ → a₁` contravariant in the domain and covariant in the codomain. Each
example is stated for every tree class, closed under the constants and the constructor
where a witness or a countermodel must lie in it, and so holds over arbitrary, regular and
finite trees. The proofs are direct: at positive arity the deciders search up to elementary
bounds and do not evaluate in practice.

## Main declarations

- `arrow`, `arr`, `tarr`, `tarr_le_tarr`: the arrow variance, arrow expressions and trees,
  and the arrow rule `a₀ → a₁ ≤ b₀ → b₁ ⟺ b₀ ≤ a₀ ∧ a₁ ≤ b₁`; `tarr_le_greatest`,
  `least_le_tarr`: `⊤ → ⊥` and `⊥ → ⊤` are the least and the greatest arrows.
- `IsParityAssignment`: parity assignments of flat systems.
- `Renaming`: both renamings of the subsumption formula are needed.
- `Identity`: the two identity schemes `∀α. α → α` and `∀βγ. (β ≤ γ) ⇒ β → γ` subsume one
  another, and the first has no parity assignment after flattening; `∀α. α → α` is below
  `β → β`, but not conversely.
- `Pottier`: `a → ⊥ ≤ a` entails `(⊥ → ⊤) → ⊥ ≤ a`, which a test through the lower bound of
  `a` misses, and the signed system without its coupling has a false countermodel.
- `SelfApp`: merging the variables of the self-application scheme
  `∀αβ. (α ≤ α → β) ⇒ α → β` into `∀γ. (γ ≤ γ → γ) ⇒ γ → γ` loses generality.
-/

namespace DeciENSSE.Examples
open DeciNSSE Core.Full Flattening Scheme

/-! ## Arrow types -/

/-- The arrow variance: the domain is contravariant and the codomain covariant. -/
def arrow : Fin 2 → Bool := ![true, false]

/-- The arrow expression `a → b`. -/
def arr {V : Type*} (a b : Term 2 V) : Term 2 V := .node ![a, b]

/-- The arrow tree `a → b`. -/
def tarr (a b : Tree 2) : Tree 2 := DeciNSSE.Tree.node ![a, b]

@[simp] theorem eval_arr {V : Type*} (ρ : V → Tree 2) (a b : Term 2 V) :
    (arr a b).eval ρ = tarr (a.eval ρ) (b.eval ρ) := by
  simp only [arr, tarr, Term.eval_node]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem map_arr {V W : Type*} (f : V → W) (a b : Term 2 V) :
    (arr a b).map f = arr (a.map f) (b.map f) := by
  simp only [arr, Term.map]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The arrow rule: `a₀ → a₁ ≤ b₀ → b₁` iff `b₀ ≤ a₀` and `a₁ ≤ b₁`. -/
theorem tarr_le_tarr (a₀ a₁ b₀ b₁ : Tree 2) :
    Tree.Le arrow (tarr a₀ a₁) (tarr b₀ b₁) ↔ Tree.Le arrow b₀ a₀ ∧ Tree.Le arrow a₁ b₁ := by
  rw [tarr, tarr, node_treeLe_node_iff]
  constructor
  · intro h
    exact ⟨by simpa [arrow] using h 0, by simpa [arrow] using h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    · simpa [arrow] using h₀
    · simpa [arrow] using h₁

@[simp] theorem tarr_ne_bot (a b : Tree 2) : tarr a b ≠ Tree.bot := Tree.node_ne_bot _

@[simp] theorem tarr_ne_top (a b : Tree 2) : tarr a b ≠ Tree.top := Tree.node_ne_top _

/-- `⊥ → ⊤` is the greatest arrow. -/
theorem tarr_le_greatest (a b : Tree 2) : Tree.Le arrow (tarr a b) (tarr Tree.bot Tree.top) :=
  (tarr_le_tarr ..).mpr ⟨bot_treeLe _ _, treeLe_top _ _⟩

/-- `⊤ → ⊥` is the least arrow. -/
theorem least_le_tarr (a b : Tree 2) : Tree.Le arrow (tarr Tree.top Tree.bot) (tarr a b) :=
  (tarr_le_tarr ..).mpr ⟨treeLe_top _ _, bot_treeLe _ _⟩

/-- An arrow tree in a class closed under the constructors. -/
theorem tarr_mem {C : Tree 2 → Prop} (hC : TermClosed C) {a b : Tree 2} (ha : C a)
    (hb : C b) : C (tarr a b) :=
  hC.node _ fun i => by fin_cases i; exacts [ha, hb]

/-! ## Parity assignments -/

/-- A parity assignment of a flat system: `π(u) = π(v)` for every literal `u ≤ v`, and
`π(aᵢ) = π(u) ⊕ c(i)` for every `i` and every literal `f(aᵢ)ᵢ ≤ u` or `u ≤ f(aᵢ)ᵢ`. -/
def IsParityAssignment {n : ℕ} {V : Type*} (c : Fin n → Bool) (χ : List (LitT n V))
    (π : V → Bool) : Prop :=
  (∀ u v, LitT.le u v ∈ χ → π u = π v) ∧
    (∀ a u, LitT.fle a u ∈ χ → ∀ i, π (a i) = Bool.xor (π u) (c i)) ∧
    (∀ u a, LitT.lef u a ∈ χ → ∀ i, π (a i) = Bool.xor (π u) (c i))

/-- An arrow literal `f(a, a) ≤ u` admits no parity assignment: it needs
`π(a) = π(u) ⊕ 1` and `π(a) = π(u)`. -/
theorem not_isParityAssignment_of_fle {V : Type*} {χ : List (LitT 2 V)} {a : Fin 2 → V}
    {u : V} (h : LitT.fle a u ∈ χ) (ha : a 0 = a 1) (π : V → Bool) :
    ¬ IsParityAssignment arrow χ π := by
  rintro ⟨-, hf, -⟩
  have h₀ : π (a 0) = Bool.xor (π u) true := hf a u h 0
  have h₁ : π (a 1) = Bool.xor (π u) false := hf a u h 1
  rw [ha, h₁] at h₀
  cases hu : π u <;> simp [hu] at h₀

/-- A copy literal `u ≤ a` with `f(a, b) ≤ u` admits no parity assignment: it needs
`π(u) = π(a)` and `π(a) = π(u) ⊕ 1`. -/
theorem not_isParityAssignment_of_le_fle {V : Type*} {χ : List (LitT 2 V)} {u v : V}
    {a : Fin 2 → V} (h₁ : LitT.le u v ∈ χ) (h₂ : LitT.fle a u ∈ χ) (ha : a 0 = v)
    (π : V → Bool) : ¬ IsParityAssignment arrow χ π := by
  rintro ⟨hl, hf, -⟩
  have e₂ : π (a 0) = Bool.xor (π u) true := hf a u h₂ 0
  rw [ha, hl u v h₁] at e₂
  cases hv : π v <;> simp [hv] at e₂

/-- Every constructor tree of arity two is an arrow. -/
theorem node_eq_tarr (b : Fin 2 → Tree 2) : DeciNSSE.Tree.node b = tarr (b 0) (b 1) := by
  rw [tarr]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Normalization of an arrow: the domain changes sign. -/
theorem normalize_tarr (s : Bool) (a b : Tree 2) :
    Tree.normalize arrow s (tarr a b) =
      tarr (Tree.normalize arrow (!s) a) (Tree.normalize arrow s b) := by
  rw [tarr, normalize_node, tarr]
  congr 1
  funext i
  fin_cases i <;> cases s <;> rfl

/-! ## Both renamings are needed -/

namespace Renaming

variable (P : Type*) [DecidableEq P] {n : ℕ}

/-- `S₁ = b`, with the free variable `b`, no bound variables and empty context. -/
def S₁ : Scheme P (Term n (Fin 1 ⊕ Empty)) := ⟨[], ∅, .var (.inl 0)⟩

/-- `S₂ = ∀b. b`; its bound variable is apart from the free `b` by construction. -/
def S₂ : Scheme P (Term n (Fin 1 ⊕ Fin 1)) := ⟨[], ∅, .var (.inr 0)⟩

/-- Read without renaming the bound variable of `S₂`, the formula would be the valid
entailment `true ⊨ b ≤ b`. -/
theorem unrenamed_valid (C : Tree n → Prop) (c : Fin n → Bool) :
    ExistsEntailsTermIn (Z := Empty) C c ([] : TermSystem n (Fin 1))
      [.le (.var (.inl 0)) (.var (.inl 0))] :=
  fun _ _ _ => ⟨Empty.elim, fun z => z.elim, by simp [TermLit.Holds, treeLe_refl]⟩

/-- With the renaming, the formula is `true ⊨ b ≤ b'`, with `b` and the bound `b'` visible. -/
theorem formula (C : Tree n → Prop) (c : Fin n → Bool) :
    SubsumesIn C c (S₁ P) (S₂ (n := n) P) ↔
      ExistsEntailsTermIn (Z := Empty) C c ([] : TermSystem n (Fin 1 ⊕ Fin 1))
        [.le (.var (.inl (.inl 0))) (.var (.inl (.inr 0)))] := by
  rw [subsumesIn_iff (by simp [S₁])]
  rfl

/-- At `b = ⊤`, the instance `⊥` of `S₂` lies above no instance of `S₁`, so `S₁ ≰ S₂`. -/
theorem not_subsumes {C : Tree n → Prop} (hC : TermClosed C) (c : Fin n → Bool) :
    ¬ SubsumesIn C c (S₁ P) (S₂ (n := n) P) := by
  intro H
  obtain ⟨_, ⟨ρ, -, -, rfl⟩, hle, -⟩ := H (fun _ => Tree.top) (fun _ => hC.top) _
    ⟨fun _ => Tree.bot, fun _ => hC.bot, by simp [S₂], rfl⟩
  simp [inst, S₁, S₂] at hle

end Renaming

/-! ## Two identity schemes -/

namespace Identity

variable (P : Type*) [DecidableEq P]

/-- `S₁ = ∀α. α → α`, with no free variables and empty context. -/
def S₁ : Scheme P (Term 2 (Empty ⊕ Fin 1)) := ⟨[], ∅, arr (.var (.inr 0)) (.var (.inr 0))⟩

/-- `S₂ = ∀βγ. (β ≤ γ) ⇒ β → γ`, with no free variables and empty context. -/
def S₂ : Scheme P (Term 2 (Empty ⊕ Fin 2)) :=
  ⟨[.le (.var (.inr 0)) (.var (.inr 1))], ∅, arr (.var (.inr 0)) (.var (.inr 1))⟩

/-- The antecedent `β ≤ γ` of `S₁ ≤ S₂`, over the visible `β, γ`. -/
def ante₁₂ : TermSystem 2 (Empty ⊕ Fin 2) := [.le (.var (.inr 0)) (.var (.inr 1))]

/-- The consequent `α → α ≤ β → γ` of `S₁ ≤ S₂`, with `α` hidden. -/
def cons₁₂ : TermSystem 2 ((Empty ⊕ Fin 2) ⊕ Fin 1) :=
  [.le (arr (.var (.inr 0)) (.var (.inr 0))) (arr (.var (.inl (.inr 0))) (.var (.inl (.inr 1))))]

/-- The consequent `β ≤ γ ∧ β → γ ≤ α → α` of `S₂ ≤ S₁`, with `α` visible and `β, γ` hidden. -/
def cons₂₁ : TermSystem 2 ((Empty ⊕ Fin 1) ⊕ Fin 2) :=
  [.le (.var (.inr 0)) (.var (.inr 1)),
    .le (arr (.var (.inr 0)) (.var (.inr 1))) (arr (.var (.inl (.inr 0))) (.var (.inl (.inr 0))))]

/-- `S₁ ≤ S₂` is `β ≤ γ ⊨ ∃α. α → α ≤ β → γ`. -/
theorem formula₁₂ (C : Tree 2 → Prop) :
    SubsumesIn C arrow (S₁ P) (S₂ P) ↔ ExistsEntailsTermIn C arrow ante₁₂ cons₁₂ := by
  rw [subsumesIn_iff (by simp [S₁])]
  simp [subsumptionGoal, goal, S₁, S₂, ante₁₂, cons₁₂, Term.map, hideBound]

/-- The inequality of the arrows says `β ≤ α` and `α ≤ γ`, and `α = β` is a witness. -/
theorem entails₁₂ (C : Tree 2 → Prop) : ExistsEntailsTermIn C arrow ante₁₂ cons₁₂ := by
  intro ρ hρ hs
  refine ⟨fun _ => ρ (.inr 0), fun _ => hρ _, ?_⟩
  simp only [ante₁₂, cons₁₂, termSat_cons, termSat_nil, and_true, TermLit.Holds, Term.eval_var,
    eval_arr, Sum.elim_inl, Sum.elim_inr] at hs ⊢
  exact (tarr_le_tarr ..).mpr ⟨treeLe_refl _ _, hs⟩

/-- `S₂ ≤ S₁` is `⊨ ∃βγ. β ≤ γ ∧ β → γ ≤ α → α`, with `α` visible. -/
theorem formula₂₁ (C : Tree 2 → Prop) :
    SubsumesIn C arrow (S₂ P) (S₁ P) ↔ ExistsEntailsTermIn C arrow [] cons₂₁ := by
  rw [subsumesIn_iff (by simp [S₂])]
  simp [subsumptionGoal, goal, S₁, S₂, cons₂₁, Term.map, TermLit.map, hideBound]

/-- The inequalities say `α ≤ β ≤ γ ≤ α`, and `β = γ = α` is a witness. -/
theorem entails₂₁ (C : Tree 2 → Prop) : ExistsEntailsTermIn C arrow [] cons₂₁ := by
  intro ρ hρ _
  refine ⟨fun _ => ρ (.inr 0), fun _ => hρ _, ?_⟩
  simp only [cons₂₁, termSat_cons, termSat_nil, and_true, TermLit.Holds, Term.eval_var,
    eval_arr, Sum.elim_inl, Sum.elim_inr]
  exact ⟨treeLe_refl _ _, treeLe_refl _ _⟩

/-- **The two identity schemes are equivalent**, in every tree class. -/
theorem equivalent (C : Tree 2 → Prop) :
    SubsumesIn C arrow (S₁ P) (S₂ P) ∧ SubsumesIn C arrow (S₂ P) (S₁ P) :=
  ⟨(formula₁₂ P C).mpr (entails₁₂ C), (formula₂₁ P C).mpr (entails₂₁ C)⟩

/-- The two identity schemes are equivalent over arbitrary, regular and finite trees. -/
theorem equivalent_classes :
    (Subsumes arrow (S₁ P) (S₂ P) ∧ Subsumes arrow (S₂ P) (S₁ P)) ∧
      (SubsumesReg arrow (S₁ P) (S₂ P) ∧ SubsumesReg arrow (S₂ P) (S₁ P)) ∧
      (SubsumesFin arrow (S₁ P) (S₂ P) ∧ SubsumesFin arrow (S₂ P) (S₁ P)) :=
  ⟨equivalent P _, equivalent P _, equivalent P _⟩

/-- After flattening, the consequent of `S₁ ≤ S₂` contains the defining literal `f(α, α) ≤ u`
of the name `u` of `α → α`, so it admits no parity assignment. -/
theorem flattened_not_parity (π : _ → Bool) :
    ¬ IsParityAssignment arrow (flattenCons (Y := Name ante₁₂) cons₁₂) π :=
  not_isParityAssignment_of_fle
    (List.mem_map_of_mem (f := LitT.map consMap) (fle_mem_flatten (φ := cons₁₂)
      (a := ![.var (.inr 0), .var (.inr 0)]) (by decide))) rfl π

/-! The example of the introduction: `∀α. α → α ≤ β → β`, but not conversely. -/

/-- `∀α. α → α`, with the free variable `β` unused. -/
def T₁ : Scheme P (Term 2 (Fin 1 ⊕ Fin 1)) := ⟨[], ∅, arr (.var (.inr 0)) (.var (.inr 0))⟩

/-- `β → β`, with `β` free. -/
def T₂ : Scheme P (Term 2 (Fin 1 ⊕ Empty)) := ⟨[], ∅, arr (.var (.inl 0)) (.var (.inl 0))⟩

/-- `∀α. α → α ≤ β → β`, with the witness `α = β`. -/
theorem intro_subsumes (C : Tree 2 → Prop) : SubsumesIn C arrow (T₁ P) (T₂ P) := by
  rw [subsumesIn_iff_forall]
  intro μ hμ _
  refine ⟨fun _ => μ (.inl 0), fun _ => hμ _, by simp [T₁], ?_⟩
  simp [SchemeInstance.Le, inst, T₁, T₂, treeLe_refl]

/-- `β → β ≰ ∀α. α → α`: at `β = ⊥`, the instance `⊤ → ⊤` lies above no instance `⊥ → ⊥`. -/
theorem intro_not_subsumes {C : Tree 2 → Prop} (hC : TermClosed C) :
    ¬ SubsumesIn C arrow (T₂ P) (T₁ P) := by
  intro H
  obtain ⟨_, ⟨ρ, -, -, rfl⟩, hle, -⟩ := H (fun _ => Tree.bot) (fun _ => hC.bot) _
    ⟨fun _ => Tree.top, fun _ => hC.top, by simp [T₁], rfl⟩
  simp [inst, T₁, T₂, tarr_le_tarr] at hle

end Identity

/-! ## A missed redundant constraint -/

namespace Pottier

variable {V : Type*}

/-- `g = ⊥ → ⊤`, the greatest arrow. -/
def g : Term 2 V := arr .bot .top

/-- `k = g → ⊥`. -/
def k : Term 2 V := arr g .bot

/-- The antecedent `C(a) = (a → ⊥ ≤ a)`, over the single variable `a`. -/
def C : TermSystem 2 (Fin 1) := [.le (arr (.var 0) .bot) (.var 0)]

/-- The tree `g`. -/
def gT : Tree 2 := tarr Tree.bot Tree.top

/-- The tree `k`. -/
def kT : Tree 2 := tarr gT Tree.bot

@[simp] theorem eval_g (ρ : V → Tree 2) : (g : Term 2 V).eval ρ = gT := by simp [g, gT]

@[simp] theorem eval_k (ρ : V → Tree 2) : (k : Term 2 V).eval ρ = kT := by simp [k, kT]

theorem termSat_C (ρ : Fin 1 → Tree 2) :
    TermSat arrow ρ C ↔ Tree.Le arrow (tarr (ρ 0) Tree.bot) (ρ 0) := by
  simp [C, TermLit.Holds]

/-- The semantic argument: `a ≠ ⊥`; if `a = ⊤`, then `k ≤ a`; otherwise `a` is an arrow, so
`a ≤ g`, and by contravariance `k = g → ⊥ ≤ a → ⊥ ≤ a`. -/
theorem kT_le {t : Tree 2} (h : Tree.Le arrow (tarr t Tree.bot) t) : Tree.Le arrow kT t := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩
  · simp at h
  · exact treeLe_top _ _
  · rw [node_eq_tarr] at h ⊢
    exact treeLe_trans ((tarr_le_tarr ..).mpr ⟨tarr_le_greatest _ _, treeLe_refl _ _⟩) h

/-- **`C ⊨ k ≤ a`** in every tree class. -/
theorem entails (D : Tree 2 → Prop) :
    ExistsEntailsTermIn (Z := Empty) D arrow C [.le k (.var (.inl 0))] := by
  intro ρ _ hs
  refine ⟨Empty.elim, fun z => z.elim, ?_⟩
  simpa [TermLit.Holds] using kT_le ((termSat_C ρ).mp hs)

/-- Equivalently, `C ⊨ ∃z. k ≤ z ∧ z ≤ a`, with the witness `z = k`, in every tree class
closed under the constructors. -/
theorem entails_exists {D : Tree 2 → Prop} (hD : TermClosed D) :
    ExistsEntailsTermIn (Z := Fin 1) D arrow C
      [.le k (.var (.inr 0)), .le (.var (.inr 0)) (.var (.inl 0))] := by
  intro ρ _ hs
  refine ⟨fun _ => kT, fun _ => tarr_mem hD (tarr_mem hD hD.bot hD.top) hD.bot, ?_⟩
  simpa [TermLit.Holds, treeLe_refl] using kT_le ((termSat_C ρ).mp hs)

/-- Through the single lower bound `a → ⊥` of `a`, the inequality `k ≤ a` needs
`k ≤ a → ⊥`, that is, `a ≤ g`. -/
theorem le_lower_iff (t : Tree 2) : Tree.Le arrow kT (tarr t Tree.bot) ↔ Tree.Le arrow t gT := by
  rw [kT, tarr_le_tarr]
  simp [treeLe_refl]

/-- `a = ⊤` satisfies `C`. -/
theorem top_sat : TermSat arrow (fun _ => Tree.top) C := by
  simp [termSat_C]

/-- `a ≤ g` is not entailed, since `a = ⊤` satisfies `C`. -/
theorem not_entails_le_g {D : Tree 2 → Prop} (hD : D Tree.top) :
    ¬ ExistsEntailsTermIn (Z := Empty) D arrow C [.le (.var (.inl 0)) g] := by
  intro H
  obtain ⟨σ, -, hs⟩ := H _ (fun _ => hD) top_sat
  simp [TermLit.Holds, gT] at hs

/-- Neither is `k ≤ a → ⊥`: a test that proves `k ≤ a` only through a lower bound of `a`
fails on this true entailment. -/
theorem not_entails_lower {D : Tree 2 → Prop} (hD : D Tree.top) :
    ¬ ExistsEntailsTermIn (Z := Empty) D arrow C [.le k (arr (.var (.inl 0)) .bot)] := by
  intro H
  obtain ⟨σ, -, hs⟩ := H _ (fun _ => hD) top_sat
  have := (le_lower_iff Tree.top).mp (by simpa [TermLit.Holds] using hs)
  simp [gT] at this

/-- After flattening, `C` has the copy literal `u ≤ a` and the defining literal `f(a, v) ≤ u`
of the name `u` of `a → ⊥`, so it admits no parity assignment. -/
theorem flattened_not_parity (π : _ → Bool) : ¬ IsParityAssignment arrow (flatten C) π :=
  not_isParityAssignment_of_le_fle (le_mem_flatten (φ := C) List.mem_cons_self)
    (fle_mem_flatten (φ := C) (a := ![.var 0, .bot]) (by decide)) rfl π

/-! ### The signed system needs its coupling -/

/-- The normalization `ν_s` for the arrow variance; `a⁺ = ν₀ a` and `a⁻ = ν₁ a`. -/
abbrev ν (s : Bool) (t : Tree 2) : Tree 2 := Tree.normalize arrow s t

/-- The signed literals `f(a⁻, ⊥) ≤ a⁺` and `a⁻ ≤ f(a⁺, ⊤)` of `a → ⊥ ≤ a`, read covariantly
on their own, for values `a⁺` and `a⁻`. -/
def SignedC (ap am : Tree 2) : Prop := tarr am Tree.bot ≤ ap ∧ am ≤ tarr ap Tree.top

/-- `C` holds at `a` exactly when its signed literals hold at `a⁺ = ν₀ a` and `a⁻ = ν₁ a`. -/
theorem signed_iff (t : Tree 2) :
    Tree.Le arrow (tarr t Tree.bot) t ↔ SignedC (ν false t) (ν true t) := by
  have h₀ := (normalize_le_normalize_iff arrow false (tarr t Tree.bot) t).symm
  have h₁ := (normalize_le_normalize_iff arrow true t (tarr t Tree.bot)).symm
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
  rw [normalize_tarr, normalize_bot] at h₀
  rw [normalize_tarr, normalize_bot] at h₁
  simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
  exact ⟨fun h => ⟨h₀.mp h, h₁.mp h⟩, fun h => h₀.mpr h.1⟩

/-- `F = f(⊥, ⊥)`. -/
def F : Tree 2 := tarr Tree.bot Tree.bot

/-- The covariant values `a⁺ = F` and `a⁻ = ⊥` satisfy the signed literals of `C`. -/
theorem decoupled_sat : SignedC F Tree.bot := ⟨le_rfl, Tree.bot_le _⟩

/-- But they violate the coupling `a⁻ = (a⁺)^∂` of the signed correspondence: no tree `a` has
`ν₀ a = F` and `ν₁ a = ⊥`. -/
theorem decoupled_not_coupled (t : Tree 2) : ¬ (ν false t = F ∧ ν true t = Tree.bot) := by
  rintro ⟨h₀, h₁⟩
  have hd : ν true t = Tree.dual (ν false t) := normalize_true arrow t
  rw [hd, h₀] at h₁
  simp [F, tarr] at h₁

/-- The signed form of `k ≤ a` requires `ν₀ k ≤ a⁺`. -/
theorem le_iff_signed (t : Tree 2) : Tree.Le arrow kT t ↔ ν false kT ≤ ν false t :=
  treeLe_iff_normalize _ _ _

/-- `ν₀ k = f(ν₁ g, ⊥) = f(F, ⊥)`. -/
theorem normalize_kT : ν false kT = tarr F Tree.bot := by
  simp [kT, gT, F, normalize_tarr, -normalize_true]

/-- `ν₀ k = f(F, ⊥) ≰ F`. -/
theorem decoupled_violates : ¬ ν false kT ≤ F := by
  rw [normalize_kT]
  intro h
  have := ((treeLe_false_iff_le _ _).mpr h)
  rw [tarr, F, tarr, node_treeLe_node_iff] at this
  have h0 := this 0
  simp at h0

/-- **A test that drops the coupling of `a⁺` and `a⁻` reports a countermodel of a true
entailment**: `C ⊨ k ≤ a` holds, while the uncoupled values `a⁺ = F`, `a⁻ = ⊥` satisfy the
signed literals of `C` and violate the signed form `ν₀ k ≤ a⁺` of `k ≤ a`. -/
theorem uncoupled_countermodel :
    ExistsEntailsTerm (Z := Empty) arrow C [.le k (.var (.inl 0))] ∧ SignedC F Tree.bot ∧
      ¬ ν false kT ≤ F :=
  ⟨entails _, decoupled_sat, decoupled_violates⟩

/-- `C ⊨ k ≤ a` over arbitrary, regular and finite trees. -/
theorem entails_classes :
    ExistsEntailsTerm (Z := Empty) arrow C [.le k (.var (.inl 0))] ∧
      ExistsEntailsTermReg (Z := Empty) arrow C [.le k (.var (.inl 0))] ∧
      ExistsEntailsTermFin (Z := Empty) arrow C [.le k (.var (.inl 0))] :=
  ⟨entails _, entails _, entails _⟩

end Pottier

/-! ## Merging the variables of self-application -/

namespace SelfApp

variable (P : Type*) [DecidableEq P]

/-- `S = ∀αβ. (α ≤ α → β) ⇒ α → β`, inferred for `λx. x x`. -/
def S : Scheme P (Term 2 (Empty ⊕ Fin 2)) :=
  ⟨[.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 1)))], ∅,
    arr (.var (.inr 0)) (.var (.inr 1))⟩

/-- `S' = ∀γ. (γ ≤ γ → γ) ⇒ γ → γ`, after merging `β` into `α`. -/
def S' : Scheme P (Term 2 (Empty ⊕ Fin 1)) :=
  ⟨[.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 0)))], ∅,
    arr (.var (.inr 0)) (.var (.inr 0))⟩

/-- The antecedent `γ ≤ γ → γ` of `S ≤ S'`. -/
def ante : TermSystem 2 (Empty ⊕ Fin 1) :=
  [.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 0)))]

/-- The consequent `α ≤ α → β ∧ α → β ≤ γ → γ` of `S ≤ S'`, with `α, β` hidden. -/
def cons : TermSystem 2 ((Empty ⊕ Fin 1) ⊕ Fin 2) :=
  [.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 1))),
    .le (arr (.var (.inr 0)) (.var (.inr 1))) (arr (.var (.inl (.inr 0))) (.var (.inl (.inr 0))))]

/-- The antecedent `α ≤ α → β` of `S' ≤ S`. -/
def ante' : TermSystem 2 (Empty ⊕ Fin 2) :=
  [.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 1)))]

/-- The consequent `γ ≤ γ → γ ∧ γ → γ ≤ α → β` of `S' ≤ S`, with `γ` hidden. -/
def cons' : TermSystem 2 ((Empty ⊕ Fin 2) ⊕ Fin 1) :=
  [.le (.var (.inr 0)) (arr (.var (.inr 0)) (.var (.inr 0))),
    .le (arr (.var (.inr 0)) (.var (.inr 0))) (arr (.var (.inl (.inr 0))) (.var (.inl (.inr 1))))]

/-- `S ≤ S'` is `γ ≤ γ → γ ⊨ ∃αβ. α ≤ α → β ∧ α → β ≤ γ → γ`. -/
theorem formula (C : Tree 2 → Prop) :
    SubsumesIn C arrow (S P) (S' P) ↔ ExistsEntailsTermIn C arrow ante cons := by
  rw [subsumesIn_iff (by simp [S])]
  simp [subsumptionGoal, goal, S, S', ante, cons, Term.map, TermLit.map, hideBound]

/-- The entailment holds with the witness `α = β = γ`. -/
theorem entails (C : Tree 2 → Prop) : ExistsEntailsTermIn C arrow ante cons := by
  intro ρ hρ hs
  refine ⟨fun _ => ρ (.inr 0), fun _ => hρ _, ?_⟩
  simp only [ante, cons, termSat_cons, termSat_nil, and_true, TermLit.Holds, Term.eval_var,
    eval_arr, Sum.elim_inl, Sum.elim_inr] at hs ⊢
  exact ⟨hs, treeLe_refl _ _⟩

/-- **`S ≤ S'`**, in every tree class. -/
theorem subsumes (C : Tree 2 → Prop) : SubsumesIn C arrow (S P) (S' P) :=
  (formula P C).mpr (entails C)

/-- `S' ≤ S` is `α ≤ α → β ⊨ ∃γ. γ ≤ γ → γ ∧ γ → γ ≤ α → β`. -/
theorem formula' (C : Tree 2 → Prop) :
    SubsumesIn C arrow (S' P) (S P) ↔ ExistsEntailsTermIn C arrow ante' cons' := by
  rw [subsumesIn_iff (by simp [S'])]
  simp [subsumptionGoal, goal, S, S', ante', cons', Term.map, TermLit.map, hideBound]

/-- The second literal says `α ≤ γ ≤ β`. -/
theorem between_iff (a b γ : Tree 2) :
    Tree.Le arrow (tarr γ γ) (tarr a b) ↔ Tree.Le arrow a γ ∧ Tree.Le arrow γ b :=
  tarr_le_tarr ..

/-- `α = ⊤ → ⊥` and `β = ⊥` satisfy the antecedent: the domain `⊤` of `α` lies above `α`,
and its codomain `⊥` below `β`. -/
theorem countermodel_sat :
    Tree.Le arrow (tarr Tree.top Tree.bot) (tarr (tarr Tree.top Tree.bot) Tree.bot) :=
  (tarr_le_tarr ..).mpr ⟨treeLe_top _ _, treeLe_refl _ _⟩

/-- No `γ` lies between the arrow `⊤ → ⊥` and `⊥`. -/
theorem no_between (γ : Tree 2) :
    ¬ (Tree.Le arrow (tarr Tree.top Tree.bot) γ ∧ Tree.Le arrow γ Tree.bot) := by
  rintro ⟨h₁, h₂⟩
  rw [treeLe_bot_iff] at h₂
  subst h₂
  simp at h₁

/-- The values of the countermodel: `α = ⊤ → ⊥`, `β = ⊥`. -/
def countermodel : Empty ⊕ Fin 2 → Tree 2 := Sum.elim Empty.elim ![tarr Tree.top Tree.bot, Tree.bot]

theorem countermodel_mem {C : Tree 2 → Prop} (hC : TermClosed C) (v : Empty ⊕ Fin 2) :
    C (countermodel v) := by
  rcases v with e | i
  · exact e.elim
  · fin_cases i
    exacts [tarr_mem hC hC.top hC.bot, hC.bot]

/-- The entailment for `S' ≤ S` fails at the countermodel, in every class that contains it. -/
theorem not_entails {C : Tree 2 → Prop} (hC : TermClosed C) :
    ¬ ExistsEntailsTermIn C arrow ante' cons' := by
  intro H
  obtain ⟨σ, -, hs⟩ := H countermodel (countermodel_mem hC)
    (by simpa [ante', countermodel, TermLit.Holds] using countermodel_sat)
  simp only [cons', termSat_cons, termSat_nil, and_true, TermLit.Holds, Term.eval_var,
    eval_arr, Sum.elim_inl, Sum.elim_inr] at hs
  exact no_between (σ 0) ((between_iff ..).mp (by simpa [countermodel] using hs.2))

/-- **`S' ≰ S`: the merge loses generality**, in every tree class closed under the
constructors. -/
theorem not_subsumes {C : Tree 2 → Prop} (hC : TermClosed C) : ¬ SubsumesIn C arrow (S' P) (S P) :=
  fun h => not_entails hC ((formula' P C).mp h)

/-- `S ≤ S'` and `S' ≰ S` over arbitrary, regular and finite trees. -/
theorem merge_loses_generality :
    (Subsumes arrow (S P) (S' P) ∧ ¬ Subsumes arrow (S' P) (S P)) ∧
      (SubsumesReg arrow (S P) (S' P) ∧ ¬ SubsumesReg arrow (S' P) (S P)) ∧
      (SubsumesFin arrow (S P) (S' P) ∧ ¬ SubsumesFin arrow (S' P) (S P)) :=
  ⟨⟨subsumes P _, not_subsumes P termClosed_all⟩, ⟨subsumes P _, not_subsumes P termClosed_reg⟩,
    ⟨subsumes P _, not_subsumes P termClosed_fin⟩⟩

/-- The instance `(⊤ → ⊥) → ⊥` of `S`, the type of `λx. x x` applied to arguments that accept
everything and return `⊥`, lies above no instance of `S'`. -/
theorem instance_above_none {C : Tree 2 → Prop} (hC : TermClosed C) (η : Empty → Tree 2) :
    (S P).IsInstance C arrow η ((S P).inst countermodel) ∧
      ((S P).inst countermodel).type = tarr (tarr Tree.top Tree.bot) Tree.bot ∧
      ∀ I, (S' P).IsInstance C arrow η I → ¬ I.Le arrow ((S P).inst countermodel) := by
  have hη : Sum.elim η ![tarr Tree.top Tree.bot, Tree.bot] = countermodel := by
    funext v; rcases v with e | i
    · exact e.elim
    · rfl
  refine ⟨⟨![tarr Tree.top Tree.bot, Tree.bot], fun i => countermodel_mem hC (.inr i), ?_, by
    rw [hη]⟩, by simp [inst, S, countermodel], ?_⟩
  · rw [hη]; simpa [S, countermodel, TermLit.Holds] using countermodel_sat
  · rintro _ ⟨ρ, -, -, rfl⟩ ⟨hle, -⟩
    simp only [inst, S, S', eval_arr, Term.eval_var, Sum.elim_inr] at hle
    exact no_between (ρ 0) ((between_iff ..).mp (by simpa [countermodel] using hle))

end SelfApp

end DeciENSSE.Examples
