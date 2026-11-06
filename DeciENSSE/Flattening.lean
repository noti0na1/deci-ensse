import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import DeciENSSE.Main
import DeciENSSE.Terms

/-! # Flattening

Flattening reduces existential entailment between systems of type expressions
(`DeciENSSE.Terms`) to existential entailment between flat systems, which the deciders of
`DeciENSSE.Core.Main` decide.

Flattening gives every distinct nonvariable subexpression `e` of a system a fresh name `v_e`;
a variable names itself. For `e = f(e₀, …, e_{n-1})` it adds the two *defining literals*
`v_e ≤ f(v_{e₀}, …, v_{e_{n-1}})` and `f(v_{e₀}, …, v_{e_{n-1}}) ≤ v_e`, and for a constant
`v_e = ⊥` or `⊤ ≤ v_e`. It replaces `e ≤ e'` by `v_e ≤ v_{e'}`, and `e = e'` by both
inequalities. The order is antisymmetric, so the defining literals say `v_e = e`: every
assignment of the variables extends in exactly one way to the names, by the values of their
expressions (`Flattening.satT_flatten`). The names of the antecedent are visible variables,
those of the consequent hidden ones. Existential entailment is preserved in every tree class
that contains the values of the subexpressions, at every variance and for both signatures,
and the flat systems have linear size.

A name is the subexpression itself (`Flattening.Name`), so equal subexpressions share one
name. The antecedent `φ` over `X` is flattened over `X ⊕ Name φ` and the consequent `ψ` over
`X ⊕ Z` over `(X ⊕ Name φ) ⊕ (Z ⊕ Name ψ)`. Over `{⊥, f}` the deciders add the top-freeness
gadget of `DeciENSSE.TopFree` on every variable of the flat systems, names included.

## Main declarations

- `Flattening.flatten`, `Flattening.flattenCons`: the flattening of an antecedent and of a
  consequent.
- `Flattening.existsEntailsTermIn_iff_flatten`: **the flattening lemma**, in every tree class
  that contains the values of the subexpressions; its six instances
  `existsEntailsTerm_iff_flatten`, …, `existsEntailsTermTopFreeFin_iff_flatten`, and
  `Flattening.top_notMem_flatten`: over `{⊥, f}` the flat systems have no literal `⊤ ≤ v`.
- `Flattening.card_name_le`, `Flattening.flatSize_flatten_le`,
  `Flattening.flatSize_flattenCons_le`: linear size.
- `decideExistsEntailsTerm`, `decideExistsEntailsTermReg`, `decideExistsEntailsTermFin` and
  `decideExistsEntailsTermTopFree`, `decideExistsEntailsTermTopFreeReg`,
  `decideExistsEntailsTermTopFreeFin`, with their `_correct` theorems.
- `existsEntailsTermReg_iff`, `existsEntailsTermTopFreeReg_iff`: regular and arbitrary
  entailment agree.
-/

namespace DeciENSSE
open DeciNSSE Core.Full

variable {n : ℕ} {V W X Y Z : Type*}

/-! ## Flattening -/

namespace Flattening

/-- The nonvariable subexpressions of a system, with repetitions. -/
def names (φ : TermSystem n V) : List (Term n V) := φ.flatMap TermLit.names

/-- The names introduced by flattening `φ`: its distinct nonvariable subexpressions. -/
abbrev Name (φ : TermSystem n V) := {e : Term n V // e ∈ names φ}

instance [DecidableEq V] (φ : TermSystem n V) : DecidableEq (Name φ) :=
  inferInstanceAs (DecidableEq {e // e ∈ names φ})

instance [DecidableEq V] (φ : TermSystem n V) : Fintype (Name φ) :=
  inferInstanceAs (Fintype {e // e ∈ names φ})

/-- The subexpressions of a constraint of `φ` are listed. -/
theorem names_subset_of_mem {φ : TermSystem n V} {l : TermLit (Term n V)} (hl : l ∈ φ) :
    l.names ⊆ names φ :=
  fun _ he => List.mem_flatMap.mpr ⟨l, hl, he⟩

/-- The listed subexpressions are closed under subexpressions. -/
theorem names_closed (φ : TermSystem n V) : ∀ e ∈ names φ, e.names ⊆ names φ := by
  intro e he
  obtain ⟨l, hl, he⟩ := List.mem_flatMap.mp he
  refine List.Subset.trans ?_ (names_subset_of_mem hl)
  cases l with
  | le t t' | eq t t' =>
    rcases List.mem_append.mp he with he | he
    · exact List.Subset.trans (Term.names_subset_of_mem he) (List.subset_append_left _ _)
    · exact List.Subset.trans (Term.names_subset_of_mem he) (List.subset_append_right _ _)

/-- No variable is listed. -/
theorem var_notMem (φ : TermSystem n V) (x : V) : Term.var x ∉ names φ := by
  intro h
  obtain ⟨l, -, he⟩ := List.mem_flatMap.mp h
  cases l with
  | le t t' | eq t t' =>
    rcases List.mem_append.mp he with he | he
    · exact Term.var_notMem_names x t he
    · exact Term.var_notMem_names x t' he

variable {L : List (Term n V)}

/-- The variable that stands for `e` after flattening: `e` itself if it is a variable, and its
name otherwise. -/
def nameOf (L : List (Term n V)) : (e : Term n V) → e.names ⊆ L → V ⊕ {e // e ∈ L}
  | .var x, _ => .inl x
  | .bot, h => .inr ⟨.bot, h (List.mem_singleton_self _)⟩
  | .top, h => .inr ⟨.top, h (List.mem_singleton_self _)⟩
  | .node a, h => .inr ⟨.node a, h List.mem_cons_self⟩

/-- The defining literals of a name: `v_e ≤ f(v_{eᵢ})ᵢ` and `f(v_{eᵢ})ᵢ ≤ v_e` for
`e = f(eᵢ)ᵢ`, `v_e = ⊥` for `e = ⊥` and `⊤ ≤ v_e` for `e = ⊤`. -/
def defining (L : List (Term n V)) (hL : ∀ e ∈ L, e.names ⊆ L) :
    {e // e ∈ L} → List (LitT n (V ⊕ {e // e ∈ L}))
  | ⟨.var _, _⟩ => []
  | ⟨.bot, h⟩ => [.bot (.inr ⟨.bot, h⟩)]
  | ⟨.top, h⟩ => [.top (.inr ⟨.top, h⟩)]
  | ⟨.node a, h⟩ =>
    [.lef (.inr ⟨.node a, h⟩) fun i =>
        nameOf L (a i) (List.Subset.trans (Term.names_child_subset a i) (hL _ h)),
      .fle (fun i => nameOf L (a i) (List.Subset.trans (Term.names_child_subset a i) (hL _ h)))
        (.inr ⟨.node a, h⟩)]

/-- The flat literals that replace a constraint: `v_e ≤ v_{e'}` for `e ≤ e'`, and both
inequalities for `e = e'`. -/
def flatLit (L : List (Term n V)) :
    (l : TermLit (Term n V)) → l.names ⊆ L → List (LitT n (V ⊕ {e // e ∈ L}))
  | .le e e', h =>
    [.le (nameOf L e (List.Subset.trans (List.subset_append_left _ _) h))
      (nameOf L e' (List.Subset.trans (List.subset_append_right _ _) h))]
  | .eq e e', h =>
    [.le (nameOf L e (List.Subset.trans (List.subset_append_left _ _) h))
      (nameOf L e' (List.Subset.trans (List.subset_append_right _ _) h)),
     .le (nameOf L e' (List.Subset.trans (List.subset_append_right _ _) h))
      (nameOf L e (List.Subset.trans (List.subset_append_left _ _) h))]

/-- **Flattening** of a system `φ` over `V`: the flat system `φ'` over `V ⊕ Name φ`, made of
the replaced constraints and the defining literals of the names. -/
def flatten (φ : TermSystem n V) : List (LitT n (V ⊕ Name φ)) :=
  φ.attach.flatMap (fun l => flatLit (names φ) l.1 (names_subset_of_mem l.2)) ++
    (names φ).attach.flatMap (defining (names φ) (names_closed φ))

/-- The replaced literal of an inequality `e ≤ e'` of `φ` belongs to the flattened system. -/
theorem le_mem_flatten {φ : TermSystem n V} {e e' : Term n V} (hl : TermLit.le e e' ∈ φ) :
    LitT.le (nameOf (names φ) e
        (List.Subset.trans (List.subset_append_left _ _) (names_subset_of_mem hl)))
      (nameOf (names φ) e'
        (List.Subset.trans (List.subset_append_right _ _) (names_subset_of_mem hl))) ∈
      flatten φ :=
  List.mem_append_left _
    (List.mem_flatMap.mpr ⟨⟨_, hl⟩, List.mem_attach _ _, List.mem_singleton_self _⟩)

/-- The upper defining literal `v_e ≤ f(v_{eᵢ})ᵢ` of a constructor name. -/
theorem lef_mem_flatten {φ : TermSystem n V} {a : Fin n → Term n V} (h : .node a ∈ names φ) :
    LitT.lef (.inr ⟨.node a, h⟩) (fun i => nameOf (names φ) (a i)
      (List.Subset.trans (Term.names_child_subset a i) (names_closed φ _ h))) ∈ flatten φ :=
  List.mem_append_right _
    (List.mem_flatMap.mpr ⟨⟨_, h⟩, List.mem_attach _ _, List.mem_cons_self⟩)

/-- The lower defining literal `f(v_{eᵢ})ᵢ ≤ v_e` of a constructor name. -/
theorem fle_mem_flatten {φ : TermSystem n V} {a : Fin n → Term n V} (h : .node a ∈ names φ) :
    LitT.fle (fun i => nameOf (names φ) (a i)
      (List.Subset.trans (Term.names_child_subset a i) (names_closed φ _ h)))
      (.inr ⟨.node a, h⟩) ∈ flatten φ :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨⟨_, h⟩, List.mem_attach _ _, List.mem_cons_of_mem _ List.mem_cons_self⟩)

/-- The placement of the variables of a flattened consequent: the visible `X` among the
visible variables `X ⊕ Y` of the flattened antecedent, the hidden `Z` and the names `W` of
the consequent among the hidden variables. -/
def consMap : (X ⊕ Z) ⊕ W → (X ⊕ Y) ⊕ (Z ⊕ W) :=
  Sum.elim (Sum.map .inl .inl) (.inr ∘ .inr)

/-- Flattening of a consequent `ψ` over `X ⊕ Z`, as a consequent with the visible variables
`X ⊕ Y` of a flattened antecedent and the hidden variables `Z ⊕ Name ψ`. -/
def flattenCons (ψ : TermSystem n (X ⊕ Z)) : List (LitT n ((X ⊕ Y) ⊕ (Z ⊕ Name ψ))) :=
  (flatten ψ).map (LitT.map consMap)

/-! ### Satisfaction of the flattened system -/

/-- `τ` gives every name the value of its expression under the values of the variables. -/
def IsNaming (L : List (Term n V)) (τ : V ⊕ {e // e ∈ L} → Tree n) : Prop :=
  ∀ e : {e // e ∈ L}, τ (.inr e) = e.1.eval (τ ∘ .inl)

/-- The extension of an assignment of the variables to the names, by the values of their
expressions. -/
def extend (L : List (Term n V)) (ρ : V → Tree n) : V ⊕ {e // e ∈ L} → Tree n :=
  Sum.elim ρ fun e => e.1.eval ρ

theorem isNaming_extend (ρ : V → Tree n) : IsNaming L (extend L ρ) := fun _ => rfl

theorem eval_nameOf_of {τ : V ⊕ {e // e ∈ L} → Tree n} {e : Term n V} (h : e.names ⊆ L)
    (he : ∀ h' : e ∈ L, τ (.inr ⟨e, h'⟩) = e.eval (τ ∘ .inl)) :
    τ (nameOf L e h) = e.eval (τ ∘ .inl) := by
  cases e with
  | var x => rfl
  | bot => exact he _
  | top => exact he _
  | node a => exact he _

theorem eval_nameOf {τ : V ⊕ {e // e ∈ L} → Tree n} (hτ : IsNaming L τ) (e : Term n V)
    (h : e.names ⊆ L) : τ (nameOf L e h) = e.eval (τ ∘ .inl) :=
  eval_nameOf_of h fun h' => hτ ⟨e, h'⟩

/-- The defining literals hold exactly when every name has the value of its expression. -/
theorem satT_defining_iff (hL : ∀ e ∈ L, e.names ⊆ L) (hv : ∀ x, Term.var x ∉ L)
    (c : Fin n → Bool) (τ : V ⊕ {e // e ∈ L} → Tree n) :
    SatT c τ (L.attach.flatMap (defining L hL)) ↔ IsNaming L τ := by
  rw [satT_flatMap]
  constructor
  · intro hs
    suffices key : ∀ (e : Term n V) (h : e ∈ L), τ (.inr ⟨e, h⟩) = e.eval (τ ∘ .inl) from
      fun e => key e.1 e.2
    intro e
    induction e with
    | var x => exact fun h => absurd h (hv x)
    | bot =>
      intro h
      exact hs ⟨.bot, h⟩ (List.mem_attach _ _) _ (List.mem_singleton_self _)
    | top =>
      intro h
      exact hs ⟨.top, h⟩ (List.mem_attach _ _) _ (List.mem_singleton_self _)
    | node a ih =>
      intro h
      have hd := hs ⟨.node a, h⟩ (List.mem_attach _ _)
      have h₁ := hd _ List.mem_cons_self
      have h₂ := hd _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HoldsT] at h₁ h₂
      rw [treeLe_antisymm h₁ h₂, Term.eval_node]
      congr 1
      funext i
      exact eval_nameOf_of _ (ih i)
  · rintro hτ ⟨e, h⟩ -
    cases e with
    | var => simp [defining, SatT]
    | bot => simpa [defining, SatT, HoldsT] using hτ ⟨.bot, h⟩
    | top => simpa [defining, SatT, HoldsT] using hτ ⟨.top, h⟩
    | node a =>
      have hc : (τ ∘ fun i =>
          nameOf L (a i) (List.Subset.trans (Term.names_child_subset a i) (hL _ h))) =
          fun i => (a i).eval (τ ∘ .inl) := funext fun i => eval_nameOf hτ _ _
      have he : τ (.inr ⟨.node a, h⟩) = DeciNSSE.Tree.node fun i => (a i).eval (τ ∘ .inl) :=
        hτ ⟨_, h⟩
      simp only [defining, SatT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, HoldsT, hc, he]
      exact ⟨treeLe_refl _ _, treeLe_refl _ _⟩

/-- Under a naming, the replaced literals of a constraint say the constraint. -/
theorem satT_flatLit {τ : V ⊕ {e // e ∈ L} → Tree n} (hτ : IsNaming L τ) (c : Fin n → Bool)
    (l : TermLit (Term n V)) (h : l.names ⊆ L) :
    SatT c τ (flatLit L l h) ↔ l.Holds c (τ ∘ .inl) := by
  cases l with
  | le e e' =>
    simp only [flatLit, SatT, List.mem_singleton, forall_eq, HoldsT, TermLit.Holds]
    rw [eval_nameOf hτ, eval_nameOf hτ]
  | eq e e' =>
    simp only [flatLit, SatT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, HoldsT, TermLit.Holds]
    rw [eval_nameOf hτ, eval_nameOf hτ]
    exact ⟨fun h => treeLe_antisymm h.1 h.2, fun h => h ▸ ⟨treeLe_refl _ _, treeLe_refl _ _⟩⟩

/-- An assignment solves the flattened system exactly when it gives every name the value of
its expression and its restriction to the variables solves the system. -/
theorem satT_flatten (c : Fin n → Bool) (φ : TermSystem n V) (τ : V ⊕ Name φ → Tree n) :
    SatT c τ (flatten φ) ↔ IsNaming (names φ) τ ∧ TermSat c (τ ∘ .inl) φ := by
  rw [flatten, satT_append, satT_defining_iff (names_closed φ) (var_notMem φ), satT_flatMap]
  constructor
  · rintro ⟨h₁, hτ⟩
    exact ⟨hτ, fun l hl => (satT_flatLit hτ c l _).mp (h₁ ⟨l, hl⟩ (List.mem_attach _ _))⟩
  · rintro ⟨hτ, h⟩
    exact ⟨fun l _ => (satT_flatLit hτ c l.1 _).mpr (h l.1 l.2), hτ⟩

/-- Satisfaction of a flattened consequent. -/
theorem satT_flattenCons (c : Fin n → Bool) (ψ : TermSystem n (X ⊕ Z))
    (ρ : X ⊕ Y → Tree n) (σ : Z ⊕ Name ψ → Tree n) :
    SatT c (Sum.elim ρ σ) (flattenCons ψ) ↔
      IsNaming (names ψ) (Sum.elim (Sum.elim (ρ ∘ .inl) (σ ∘ .inl)) (σ ∘ .inr)) ∧
        TermSat c (Sum.elim (ρ ∘ .inl) (σ ∘ .inl)) ψ := by
  have hm : Sum.elim ρ σ ∘ consMap = Sum.elim (Sum.elim (ρ ∘ .inl) (σ ∘ .inl)) (σ ∘ .inr) := by
    funext v; rcases v with (x | z) | e <;> rfl
  rw [flattenCons, satT_map, hm, satT_flatten]
  rfl

/-! ### The flattening lemma -/

/-- The class `C` contains the value of every listed expression at every assignment of trees
of `C` to its variables. -/
def EvalClosed (C : Tree n → Prop) (L : List (Term n V)) : Prop :=
  ∀ ρ : V → Tree n, (∀ v, C (ρ v)) → ∀ e ∈ L, C (e.eval ρ)

theorem _root_.DeciENSSE.TermClosed.evalClosed {C : Tree n → Prop} (hC : TermClosed C)
    (L : List (Term n V)) : EvalClosed C L :=
  fun _ hρ e _ => hC.eval hρ e

/-- The subexpressions of a system over `{⊥, f}` have values in every class closed under `⊥`
and the constructor. -/
theorem _root_.DeciENSSE.BFTermClosed.evalClosed {C : Tree n → Prop} (hC : BFTermClosed C)
    (φ : BFTermSystem n V) : EvalClosed C (names (φ.map (TermLit.map BFTerm.toTerm))) := by
  intro ρ hρ e he
  obtain ⟨l, hl, he⟩ := List.mem_flatMap.mp he
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hl
  have : ∃ b : BFTerm n V, b.toTerm = e := by
    cases l with
    | le t t' | eq t t' =>
      rcases List.mem_append.mp he with he | he
      · exact BFTerm.exists_of_mem_names he
      · exact BFTerm.exists_of_mem_names he
  obtain ⟨b, rfl⟩ := this
  exact hC.eval hρ b

/-- **The flattening lemma.** In a tree class `C` that contains the values of the
subexpressions of both systems, `φ ⊨ ∃ z̄. ψ` holds exactly when the flattened antecedent
entails the flattened consequent, whose hidden variables are those of `ψ` and its names. The
variance is arbitrary. -/
theorem existsEntailsTermIn_iff_flatten {C : Tree n → Prop} {c : Fin n → Bool}
    {φ : TermSystem n X} {ψ : TermSystem n (X ⊕ Z)} (hφ : EvalClosed C (names φ))
    (hψ : EvalClosed C (names ψ)) :
    ExistsEntailsTermIn C c φ ψ ↔ ExistsEntailsTIn C c (flatten φ) (flattenCons ψ) := by
  constructor
  · intro H ρ hρ hs
    obtain ⟨-, hφs⟩ := (satT_flatten c φ ρ).mp hs
    obtain ⟨σ, hσ, hψs⟩ := H (ρ ∘ .inl) (fun x => hρ _) hφs
    have hμ : ∀ v, C (Sum.elim (ρ ∘ .inl) σ v) := by
      rintro (x | z)
      exacts [hρ _, hσ z]
    refine ⟨Sum.elim σ fun e => e.1.eval (Sum.elim (ρ ∘ .inl) σ), ?_, ?_⟩
    · rintro (z | e)
      exacts [hσ z, hψ _ hμ e.1 e.2]
    · rw [satT_flattenCons]
      exact ⟨isNaming_extend _, hψs⟩
  · intro H ρ hρ hs
    have hext : ∀ v, C (extend (names φ) ρ v) := by
      rintro (x | e)
      exacts [hρ x, hφ ρ hρ e.1 e.2]
    obtain ⟨σ, hσ, hψs⟩ := H _ hext ((satT_flatten c φ _).mpr ⟨isNaming_extend _, hs⟩)
    exact ⟨σ ∘ .inl, fun z => hσ _, ((satT_flattenCons c ψ _ σ).mp hψs).2⟩

/-! ### Size

Every distinct nonvariable subexpression gets one name and at most two defining literals,
each with at most `n + 1` variables. Counting variable occurrences of flat literals
(`flatSize`) and symbols of expressions (`size`), the flattened system has at most six
variable occurrences per symbol of the original, independently of the arity. -/

/-- The number of variable occurrences of a flat literal. -/
def flatSize : LitT n V → ℕ
  | .le _ _ => 2
  | .fle _ _ => n + 1
  | .lef _ _ => n + 1
  | .bot _ => 1
  | .top _ => 1

@[simp] theorem flatSize_map (f : V → W) (l : LitT n V) : flatSize (l.map f) = flatSize l := by
  cases l <;> rfl

/-- The number of symbols of a system. -/
def size (φ : TermSystem n V) : ℕ := (φ.map TermLit.size).sum

private theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_map_le_sum_map {α : Type*} (l : List α) {f g : α → ℕ}
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum :=
  List.sum_le_sum h

/-- The number of variable occurrences of the defining literals of an expression. -/
def definingSize : Term n V → ℕ
  | .var _ => 0
  | .bot => 1
  | .top => 1
  | .node _ => 2 * (n + 1)

theorem flatSize_defining (hL : ∀ e ∈ L, e.names ⊆ L) (e : {e // e ∈ L}) :
    ((defining L hL e).map flatSize).sum = definingSize e.1 := by
  obtain ⟨e, h⟩ := e
  cases e with
  | node => simp [defining, flatSize, definingSize]; omega
  | _ => simp [defining, flatSize, definingSize]

/-- The defining literals of the subexpressions of `t` have fewer than `4 · size t` variable
occurrences. -/
theorem definingSize_names_le (t : Term n V) :
    (t.names.map definingSize).sum + 2 ≤ 4 * t.size := by
  induction t with
  | var => simp [Term.names, Term.size]
  | bot => simp [Term.names, Term.size, definingSize]
  | top => simp [Term.names, Term.size, definingSize]
  | node a ih =>
    have hs : ∑ i, ((((a i).names.map definingSize).sum) + 2) ≤ ∑ i, 4 * (a i).size :=
      Finset.sum_le_sum fun i _ => ih i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
    simp only [Term.names, Term.size, List.map_cons, List.sum_cons, definingSize,
      sum_flatMap_map, ← Fin.sum_univ_def] at hs ⊢
    omega

theorem flatSize_flatLit_le (l : TermLit (Term n V)) (h : l.names ⊆ L) :
    ((flatLit L l h).map flatSize).sum ≤ 2 * l.size := by
  cases l with
  | le e e' =>
    have := e.size_pos; have := e'.size_pos
    simp [flatLit, flatSize, TermLit.size]; omega
  | eq e e' =>
    have := e.size_pos; have := e'.size_pos
    simp [flatLit, flatSize, TermLit.size]; omega

/-- **Linear size.** The flattened system has at most `6 · size φ` variable occurrences. -/
theorem flatSize_flatten_le (φ : TermSystem n V) :
    ((flatten φ).map flatSize).sum ≤ 6 * size φ := by
  have h₁ : ((φ.attach.flatMap fun l => flatLit (names φ) l.1 (names_subset_of_mem l.2)).map
      flatSize).sum ≤ 2 * size φ := by
    rw [sum_flatMap_map]
    calc _ ≤ (φ.attach.map fun l => 2 * l.1.size).sum :=
          sum_map_le_sum_map _ fun l _ => flatSize_flatLit_le _ _
      _ = 2 * size φ := by
        rw [List.attach_map_val (f := fun l : TermLit (Term n V) => 2 * l.size),
          List.sum_map_mul_left, size]
  have h₂ : (((names φ).attach.flatMap (defining (names φ) (names_closed φ))).map
      flatSize).sum ≤ 4 * size φ := by
    rw [sum_flatMap_map]
    simp only [flatSize_defining]
    rw [List.attach_map_val (f := definingSize), names, sum_flatMap_map, size,
      ← List.sum_map_mul_left]
    apply sum_map_le_sum_map
    intro l _
    cases l with
    | le e e' | eq e e' =>
      have := definingSize_names_le e
      have := definingSize_names_le e'
      simp only [TermLit.names, TermLit.size, List.map_append, List.sum_append]
      omega
  rw [flatten, List.map_append, List.sum_append]
  omega

/-- The flattened consequent has the size of the flattened system. -/
theorem flatSize_flattenCons_le (ψ : TermSystem n (X ⊕ Z)) :
    ((flattenCons (Y := Y) ψ).map flatSize).sum ≤ 6 * size ψ := by
  simpa [flattenCons, Function.comp_def] using flatSize_flatten_le ψ

/-- **Linear size.** At most one name per symbol. -/
theorem card_name_le [DecidableEq V] (φ : TermSystem n V) : Fintype.card (Name φ) ≤ size φ := by
  have hs : Function.Surjective fun i : Fin (names φ).length =>
      (⟨(names φ)[i], List.getElem_mem _⟩ : Name φ) := by
    rintro ⟨e, he⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨⟨i, hi⟩, rfl⟩
  refine (Fintype.card_le_of_surjective _ hs).trans ?_
  rw [Fintype.card_fin, names, List.length_flatMap, size]
  apply sum_map_le_sum_map
  intro l _
  cases l with
  | le e e' | eq e e' =>
    have := e.length_names_le
    have := e'.length_names_le
    simp only [TermLit.names, TermLit.size, List.length_append]
    omega

end Flattening

/-! ## The flattening lemma in the three tree classes and both signatures -/

open Flattening

/-- Flattening over arbitrary trees, for every variance. -/
theorem existsEntailsTerm_iff_flatten (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    ExistsEntailsTerm c φ ψ ↔ ExistsEntailsT c (flatten φ) (flattenCons ψ) :=
  existsEntailsTermIn_iff_flatten (termClosed_all.evalClosed _) (termClosed_all.evalClosed _)

/-- Flattening over regular trees, for every variance. -/
theorem existsEntailsTermReg_iff_flatten (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    ExistsEntailsTermReg c φ ψ ↔ ExistsEntailsTReg c (flatten φ) (flattenCons ψ) :=
  (existsEntailsTermIn_iff_flatten (termClosed_reg.evalClosed _)
    (termClosed_reg.evalClosed _)).trans (existsEntailsTReg_iff _ _ _).symm

/-- Flattening over finite trees, for every variance. -/
theorem existsEntailsTermFin_iff_flatten (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    ExistsEntailsTermFin c φ ψ ↔ ExistsEntailsTFin c (flatten φ) (flattenCons ψ) :=
  (existsEntailsTermIn_iff_flatten (termClosed_fin.evalClosed _)
    (termClosed_fin.evalClosed _)).trans (existsEntailsTFin_iff _ _ _).symm

/-- Flattening over top-free trees, for systems over `{⊥, f}`. -/
theorem existsEntailsTermTopFree_iff_flatten (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFree φ ψ ↔
      ExistsEntailsTIn TopFree (fun _ => false) (flatten (φ.map (TermLit.map BFTerm.toTerm)))
        (flattenCons (ψ.map (TermLit.map BFTerm.toTerm))) :=
  existsEntailsTermIn_iff_flatten (bfTermClosed_topFree.evalClosed φ)
    (bfTermClosed_topFree.evalClosed ψ)

/-- Flattening over top-free regular trees, for systems over `{⊥, f}`. -/
theorem existsEntailsTermTopFreeReg_iff_flatten (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFreeReg φ ψ ↔
      ExistsEntailsTIn (fun t => TopFree t ∧ ∃ g : RGraph n, g.unfold = t) (fun _ => false)
        (flatten (φ.map (TermLit.map BFTerm.toTerm)))
        (flattenCons (ψ.map (TermLit.map BFTerm.toTerm))) :=
  existsEntailsTermIn_iff_flatten (termClosed_reg.topFree.evalClosed φ)
    (termClosed_reg.topFree.evalClosed ψ)

/-- Flattening over top-free finite trees, for systems over `{⊥, f}`. -/
theorem existsEntailsTermTopFreeFin_iff_flatten (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFreeFin φ ψ ↔
      ExistsEntailsTIn (fun t => TopFree t ∧ ∃ a : FTree n, a.toTree = t) (fun _ => false)
        (flatten (φ.map (TermLit.map BFTerm.toTerm)))
        (flattenCons (ψ.map (TermLit.map BFTerm.toTerm))) :=
  existsEntailsTermIn_iff_flatten (termClosed_fin.topFree.evalClosed φ)
    (termClosed_fin.topFree.evalClosed ψ)

/-- Over `{⊥, f}` the flattened system is a system over `{⊥, f}`: it has no literal `⊤ ≤ v`. -/
theorem Flattening.top_notMem_flatten (φ : BFTermSystem n V) (u) :
    LitT.top u ∉ flatten (φ.map (TermLit.map BFTerm.toTerm)) := by
  have htop : Term.top ∉ names (φ.map (TermLit.map BFTerm.toTerm)) := fun h => by
    obtain ⟨l, hl, he⟩ := List.mem_flatMap.mp h
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hl
    have : ∃ b : BFTerm n V, b.toTerm = .top := by
      cases l with
      | le t t' | eq t t' =>
        rcases List.mem_append.mp he with he | he
        · exact BFTerm.exists_of_mem_names he
        · exact BFTerm.exists_of_mem_names he
    obtain ⟨b, hb⟩ := this
    cases b <;> simp [BFTerm.toTerm] at hb
  intro h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨l, _⟩, -, h⟩ := List.mem_flatMap.mp h
    cases l <;> simp [flatLit] at h
  · obtain ⟨⟨e, he⟩, -, h⟩ := List.mem_flatMap.mp h
    cases e with
    | top => exact htop he
    | var | bot | node => simp [defining] at h

/-! ## Deciders -/

namespace Flattening

/-- Decide `p` with a procedure that may use a complete list of the elements of a finite type.
The list comes from the truncated enumeration `Fintype.truncEquivFin`, and the decision does
not depend on it. -/
@[instance_reducible] def decidableOfCompleteList {α : Type*} [Fintype α] [DecidableEq α]
    {p : Prop} (d : (xs : List α) → (∀ x, x ∈ xs) → Decidable p) : Decidable p :=
  Trunc.lift (fun e : α ≃ Fin (Fintype.card α) => d ((List.finRange _).map e.symm) fun x =>
      List.mem_map.mpr ⟨e x, List.mem_finRange _, e.symm_apply_apply x⟩)
    (fun _ _ => Subsingleton.elim _ _) (Fintype.truncEquivFin α)

/-- A complete list of the variables of a flattened system, from a list of the original
variables. -/
def varList {T : Type*} (xs : List V) (L : List T) : List (V ⊕ {e // e ∈ L}) :=
  xs.map .inl ++ L.attach.map .inr

theorem mem_varList {T : Type*} {xs : List V} (hxs : ∀ x, x ∈ xs) (L : List T) :
    ∀ v, v ∈ varList xs L := by
  rintro (x | e)
  · exact List.mem_append_left _ (List.mem_map_of_mem (hxs x))
  · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_attach _ e))

end Flattening

/-- Over `{⊥, f}`, flattening followed by the top-freeness gadget on every variable gives
full-signature entailment at the covariant variance, over arbitrary trees. -/
theorem existsEntailsTermTopFree_iff_core {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z}
    (hzs : ∀ z, z ∈ zs) (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFree φ ψ ↔
      ExistsEntailsT (fun _ => false) (TopFree.gadgetAnte (varList xs _) (flatten _))
        (TopFree.gadgetCons (varList zs _)
          (flattenCons (Y := Name (φ.map (TermLit.map BFTerm.toTerm)))
            (ψ.map (TermLit.map BFTerm.toTerm)))) :=
  (existsEntailsTermTopFree_iff_flatten φ ψ).trans
    (TopFree.existsEntailsT_iff_gadget (mem_varList hxs _) (mem_varList hzs _) _ _)

/-- The same over regular trees. -/
theorem existsEntailsTermTopFreeReg_iff_core {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z}
    (hzs : ∀ z, z ∈ zs) (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFreeReg φ ψ ↔
      ExistsEntailsTReg (fun _ => false) (TopFree.gadgetAnte (varList xs _) (flatten _))
        (TopFree.gadgetCons (varList zs _)
          (flattenCons (Y := Name (φ.map (TermLit.map BFTerm.toTerm)))
            (ψ.map (TermLit.map BFTerm.toTerm)))) :=
  (existsEntailsTermTopFreeReg_iff_flatten φ ψ).trans
    (TopFree.existsEntailsTReg_iff_gadget (mem_varList hxs _) (mem_varList hzs _) _ _)

/-- The same over finite trees. -/
theorem existsEntailsTermTopFreeFin_iff_core {xs : List X} (hxs : ∀ x, x ∈ xs) {zs : List Z}
    (hzs : ∀ z, z ∈ zs) (φ : BFTermSystem n X) (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFreeFin φ ψ ↔
      ExistsEntailsTFin (fun _ => false) (TopFree.gadgetAnte (varList xs _) (flatten _))
        (TopFree.gadgetCons (varList zs _)
          (flattenCons (Y := Name (φ.map (TermLit.map BFTerm.toTerm)))
            (ψ.map (TermLit.map BFTerm.toTerm)))) :=
  (existsEntailsTermTopFreeFin_iff_flatten φ ψ).trans
    (TopFree.existsEntailsTFin_iff_gadget (mem_varList hxs _) (mem_varList hzs _) _ _)

section Deciders

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Decide existential entailment between systems of expressions over arbitrary trees. -/
@[instance_reducible] def decideExistsEntailsTerm (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTerm c φ ψ) := by
  letI := Core.Main.decideExistsEntails c (flatten φ) (flattenCons ψ)
  exact decidable_of_iff _ (existsEntailsTerm_iff_flatten c φ ψ).symm

/-- The decision returns true exactly when arbitrary-tree entailment holds. -/
theorem decideExistsEntailsTerm_correct (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTerm c φ ψ) = true ↔ ExistsEntailsTerm c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTerm c φ ψ)

/-- Decide existential entailment between systems of expressions over regular trees. -/
@[instance_reducible] def decideExistsEntailsTermReg (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermReg c φ ψ) := by
  letI := Core.Main.decideExistsEntailsReg c (flatten φ) (flattenCons ψ)
  exact decidable_of_iff _ (existsEntailsTermReg_iff_flatten c φ ψ).symm

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideExistsEntailsTermReg_correct (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTermReg c φ ψ) = true ↔ ExistsEntailsTermReg c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTermReg c φ ψ)

/-- Decide existential entailment between systems of expressions over finite trees. -/
@[instance_reducible] def decideExistsEntailsTermFin (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermFin c φ ψ) := by
  letI := Core.Main.decideExistsEntailsFin c (flatten φ) (flattenCons ψ)
  exact decidable_of_iff _ (existsEntailsTermFin_iff_flatten c φ ψ).symm

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideExistsEntailsTermFin_correct (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTermFin c φ ψ) = true ↔ ExistsEntailsTermFin c φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTermFin c φ ψ)

/-- Decide covariant existential entailment between systems over `{⊥, f}`, over top-free
trees. -/
@[instance_reducible] def decideExistsEntailsTermTopFree (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermTopFree φ ψ) :=
  decidableOfCompleteList (α := X) fun _ hxs => decidableOfCompleteList (α := Z) fun _ hzs =>
    @decidable_of_iff _ _ (existsEntailsTermTopFree_iff_core hxs hzs φ ψ).symm
      (Core.Main.decideExistsEntails _ _ _)

/-- The decision returns true exactly when top-free entailment holds. -/
theorem decideExistsEntailsTermTopFree_correct (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTermTopFree φ ψ) = true ↔ ExistsEntailsTermTopFree φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTermTopFree φ ψ)

/-- Decide covariant existential entailment between systems over `{⊥, f}`, over top-free
regular trees. -/
@[instance_reducible] def decideExistsEntailsTermTopFreeReg (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermTopFreeReg φ ψ) :=
  decidableOfCompleteList (α := X) fun _ hxs => decidableOfCompleteList (α := Z) fun _ hzs =>
    @decidable_of_iff _ _ (existsEntailsTermTopFreeReg_iff_core hxs hzs φ ψ).symm
      (Core.Main.decideExistsEntailsReg _ _ _)

/-- The decision returns true exactly when top-free regular entailment holds. -/
theorem decideExistsEntailsTermTopFreeReg_correct (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTermTopFreeReg φ ψ) = true ↔
      ExistsEntailsTermTopFreeReg φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTermTopFreeReg φ ψ)

/-- Decide covariant existential entailment between systems over `{⊥, f}`, over top-free
finite trees. -/
@[instance_reducible] def decideExistsEntailsTermTopFreeFin (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermTopFreeFin φ ψ) :=
  decidableOfCompleteList (α := X) fun _ hxs => decidableOfCompleteList (α := Z) fun _ hzs =>
    @decidable_of_iff _ _ (existsEntailsTermTopFreeFin_iff_core hxs hzs φ ψ).symm
      (Core.Main.decideExistsEntailsFin _ _ _)

/-- The decision returns true exactly when top-free finite entailment holds. -/
theorem decideExistsEntailsTermTopFreeFin_correct (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    @decide _ (decideExistsEntailsTermTopFreeFin φ ψ) = true ↔
      ExistsEntailsTermTopFreeFin φ ψ :=
  @decide_eq_true_iff _ (decideExistsEntailsTermTopFreeFin φ ψ)

end Deciders

/-! ## Regular and arbitrary trees agree -/

/-- Over `{⊥, f, ⊤}`, regular and arbitrary entailment between systems of expressions agree. -/
theorem existsEntailsTermReg_iff [Fintype X] [Fintype Z] (c : Fin n → Bool)
    (φ : TermSystem n X) (ψ : TermSystem n (X ⊕ Z)) :
    ExistsEntailsTermReg c φ ψ ↔ ExistsEntailsTerm c φ ψ := by
  classical
  rw [existsEntailsTermReg_iff_flatten, existsEntailsTerm_iff_flatten]
  exact Core.Mixed.existsEntailsTReg_iff_mixed _ _ _

/-- Over `{⊥, f}`, regular and arbitrary entailment between systems of expressions agree. -/
theorem existsEntailsTermTopFreeReg_iff [Fintype X] [Fintype Z] (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) :
    ExistsEntailsTermTopFreeReg φ ψ ↔ ExistsEntailsTermTopFree φ ψ := by
  classical
  have hxs : ∀ x : X, x ∈ (Finset.univ : Finset X).toList := by simp
  have hzs : ∀ z : Z, z ∈ (Finset.univ : Finset Z).toList := by simp
  rw [existsEntailsTermTopFreeReg_iff_core hxs hzs, existsEntailsTermTopFree_iff_core hxs hzs]
  exact Core.Mixed.existsEntailsTReg_iff_mixed _ _ _

end DeciENSSE
