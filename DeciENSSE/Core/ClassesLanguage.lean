import DeciENSSE.Core.AutomataDecide
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.List

/-! # Regular constructor languages and Horn hulls

A constructor language is regular when it has finitely many residuals.
Finite automata recognize the least forced-atom solution, and upper/lower
summaries express a Horn hull using unions and concatenations of regular
languages. Thus regular seed assignments have regular least extensions;
in particular, least solutions and singleton seed closures are regular.

These are the language facts used by `Core/Classes` to transfer the covariant
entailment criterion from arbitrary trees to regular trees.

## Main declarations

- `Classes.Reg`, `Classes.reg_mul`, `Classes.reg_dfa`: finite residuals,
  concatenation, and automaton recognition.
- `Classes.hull_language`: the upper/lower summary formula for a Horn hull.
- `Classes.mu_regular`, `Classes.hull_regular`, `Classes.cl_regular`:
  regularity of forced atoms, regular-seed hulls, and singleton closures.
-/

namespace DeciENSSE.Core.Classes
open DeciENSSE.Core.Words
variable {n : ℕ}

/-- A language of constructor positions. -/
abbrev Lang (n : ℕ) := Set (List (Fin n))
/-- Concatenation of two position languages. -/
def cat (A B : Lang n) : Lang n := {w | ∃ a ∈ A, ∃ b ∈ B, a ++ b = w}
/-- The residual language after a prefix. -/
abbrev quot (L : Lang n) (u : List (Fin n)) : Lang n := {v | u ++ v ∈ L}
/-- A language is regular when it has finitely many residuals. -/
def Reg (L : Lang n) : Prop := (Set.range (quot L)).Finite

/-- The residual at the empty prefix is the original language. -/
@[simp] theorem quot_nil (L : Lang n) : quot L [] = L := rfl

/-- Residuals compose along appended prefixes. -/
theorem quot_append (L : Lang n) (u v : List (Fin n)) :
    quot L (u ++ v) = quot (quot L u) v := by
  ext w; simp [quot, List.append_assoc]

/-- A finite family closed under letter residuals proves regularity. -/
theorem reg_of_closed {F : Set (Lang n)} (hf : F.Finite) {L : Lang n}
    (hl : L ∈ F) (hc : ∀ A ∈ F, ∀ c, quot A [c] ∈ F) : Reg L := by
  apply hf.subset
  rintro _ ⟨u,rfl⟩
  induction u using List.reverseRecOn with
  | nil => exact hl
  | append_singleton u c ih => rw [quot_append]; exact hc _ ih c

/-- Residuals of a recognized language are determined by reached states. -/
theorem reg_dfa {S : Type*} [Finite S] (M : LDFA (Fin n) S) (F : Set S) :
    Reg {w | M.run w ∈ F} := by
  apply (Set.finite_range (fun q => {v | M.runFrom q v ∈ F})).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨M.run u, by ext v; simp [quot, LDFA.run, LDFA.runFrom_append]⟩

/-- Residuals of regular languages are regular. -/
theorem reg_residual {L : Lang n} (h : Reg L) (u : List (Fin n)) : Reg (quot L u) := by
  apply h.subset
  rintro _ ⟨v,rfl⟩
  exact ⟨u ++ v, quot_append L u v⟩

/-- A union of two regular languages is regular. -/
theorem reg_union {A B : Lang n} (ha : Reg A) (hb : Reg B) : Reg (A ∪ B) := by
  apply (ha.image2 (· ∪ ·) hb).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨quot A u, ⟨u,rfl⟩, quot B u, ⟨u,rfl⟩, rfl⟩

/-- The empty language is regular. -/
theorem reg_empty : Reg (∅ : Lang n) := by
  have he : Set.range (quot (∅ : Lang n)) = {∅} := by ext L; simp [quot, eq_comm]
  rw [Reg, he]; exact Set.finite_singleton _

/-- A finite union of regular languages is regular. -/
theorem reg_sUnion {F : Set (Lang n)} (hf : F.Finite) (h : ∀ L ∈ F, Reg L) :
    Reg (⋃₀ F) := by
  induction F, hf using Set.Finite.induction_on with
  | empty => simpa using (reg_empty (n := n))
  | @insert L F hn hf ih =>
    rw [Set.sUnion_insert]
    exact reg_union (h L (by simp)) (ih (fun A hA => h A (by simp [hA])))

/-- Every finite language is regular. -/
theorem reg_finite {L : Lang n} (hf : L.Finite) : Reg L := by
  let R : Lang n := ⋃ w ∈ L, {v | v.IsSuffix w}
  have hR : R.Finite := hf.biUnion fun w _ => by
    apply (List.finite_length_le (Fin n) w.length).subset
    exact fun _ hv => hv.length_le
  apply (hR.powerset).subset
  rintro _ ⟨u,rfl⟩ v hv
  exact Set.mem_iUnion.mpr ⟨u ++ v, Set.mem_iUnion.mpr ⟨hv, u, rfl⟩⟩

/-- One-letter derivative of concatenation, proved by splitting its first word. -/
theorem quot_mul (A B : Lang n) (c : Fin n) :
    quot (cat A B) [c] =
      cat (quot A [c]) B ∪
        {v | [] ∈ A ∧ c :: v ∈ B} := by
  classical
  ext v
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    cases a with
    | nil =>
      right
      simp only [List.nil_append] at he
      subst b
      exact ⟨ha, hb⟩
    | cons d a =>
      have he' := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := he'
      exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | h)
    · exact ⟨c :: a, ha, b, hb, rfl⟩
    · exact ⟨[], h.1, c :: v, h.2, rfl⟩

/-- Concatenation has finite residuals: a residual of A and a subset of residuals of B determine
each residual of A·B. -/
theorem reg_mul {A B : Lang n} (ha : Reg A) (hb : Reg B) :
    Reg (cat A B) := by
  classical
  let R := Set.range (quot B)
  let F : Set (Lang n) := Set.image2 (fun a T =>
    cat a B ∪ ⋃₀ T) (Set.range (quot A)) (𝒫 R)
  apply reg_of_closed (ha.image2 _ hb.powerset) (F := F)
  · exact ⟨A, ⟨[], rfl⟩, ∅, Set.empty_subset _, by simp⟩
  · rintro L ⟨a, ⟨u,rfl⟩, T, hT, rfl⟩ c
    let T' : Set (Lang n) := (fun l => quot l [c]) '' T ∪
      (if [] ∈ quot A u then {quot B [c]} else ∅)
    refine ⟨quot A (u ++ [c]), ⟨u ++ [c],rfl⟩, T', ?_, ?_⟩
    · rintro L (⟨l,hl,rfl⟩ | hl)
      · obtain ⟨v,rfl⟩ := hT hl
        exact ⟨v ++ [c], quot_append _ _ _⟩
      · by_cases he : [] ∈ quot A u
        · simp only [he, ite_true, Set.mem_singleton_iff] at hl
          exact hl ▸ ⟨[c], rfl⟩
        · simp [he] at hl
    · rw [quot_append]
      have hq : quot ((cat (quot A u) B ∪ ⋃₀ T)) [c] =
          quot (cat (quot A u) B) [c] ∪
            ⋃₀ ((fun l => quot l [c]) '' T) := by
        ext v; simp [quot]
      rw [hq, quot_mul]
      dsimp only [T']
      rw [Set.sUnion_union]
      ext v
      by_cases he : [] ∈ quot A u <;> simp [he, or_assoc, or_left_comm, or_comm]

open DeciENSSE.Core.Automata
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Regularity of μ follows directly from the lower automaton state. -/
theorem mu_regular (χ : List (Lit n V)) (y : V) :
    IsRegularTree (assignmentOf (Mu χ) mu_closed.prefixClosed y) := by
  have h := reg_dfa (lower χ y) {q | (q ∩ LowF χ).Nonempty}
  change Reg {w | (y,w) ∈ Mu χ}
  change Reg {w | (Q χ y w ∩ LowF χ).Nonempty} at h
  simpa only [mu_membership] using h

/-- All possible residual seed languages after an upper-automaton cut. -/
def seedResiduals (χ : List (Lit n V)) (ρ : V → (BFTree n)) (r : V) : Set (Lang n) :=
  {L | ∃ x β, r ∈ P χ x β ∧ L = quot (ρ x).K β}

/-- The possible residual tails supplied by a seed assignment. -/
def seedTail (χ : List (Lit n V)) (ρ : V → (BFTree n)) (r : V) : Lang n :=
  ⋃₀ seedResiduals χ ρ r

/-- Regular seed assignments give regular tail languages. -/
theorem seedTail_regular (χ : List (Lit n V)) (ρ : V → (BFTree n))
    (hr : ∀ x, IsRegularTree (ρ x)) (r : V) : Reg (seedTail χ ρ r) := by
  have hR : (⋃ x, Set.range (quot (ρ x).K)).Finite := Set.finite_iUnion hr
  have hf : (seedResiduals χ ρ r).Finite := hR.subset (by
    rintro L ⟨x,β,_,rfl⟩
    exact Set.mem_iUnion.mpr ⟨x, β, rfl⟩)
  apply reg_sUnion hf
  rintro L ⟨x,β,_,rfl⟩
  exact reg_residual (hr x) β

/-- The normal-form expression for the hull of a prefix-closed seed tuple. -/
theorem hull_language (χ : List (Lit n V)) (ρ : V → (BFTree n)) (y : V) :
    {t | (y,t) ∈ Hull χ (configSet ρ)} = {t | (y,t) ∈ Mu χ} ∪
      ⋃ r, cat {γ | r ∈ Q χ y γ} (seedTail χ ρ r) := by
  ext t
  constructor
  · rintro (hm | ⟨⟨x,u⟩,hu,hr⟩)
    · exact Or.inl hm
    · change u ∈ (ρ x).K at hu
      rcases cl_membership.mp (Or.inr hr : (y,t) ∈ Cl χ (x,u)) with
        hm | ⟨s,hs,e,he,hq,hp⟩
      · exact Or.inl (mu_membership.mpr hm)
      · obtain ⟨r,hr⟩ := hq
        obtain ⟨hp',hq'⟩ := Finset.mem_inter.mp hr
        right
        apply Set.mem_iUnion.mpr
        refine ⟨r, t.take e, hq', t.drop e, ?_, List.take_append_drop e t⟩
        refine ⟨quot (ρ x).K (u.take s), ⟨x, u.take s, hp', rfl⟩, ?_⟩
        obtain ⟨v,hv⟩ := hp
        apply (ρ x).prefix_closed (u.take s ++ t.drop e) v
        simpa only [List.append_assoc, hv, List.take_append_drop] using hu
  · rintro (hm | ht)
    · exact Or.inl hm
    · obtain ⟨r,γ,hq,σ,⟨L,⟨x,β,hp,rfl⟩,hσ⟩,rfl⟩ := Set.mem_iUnion.mp ht
      refine Or.inr ⟨(x,β ++ σ), hσ, ?_⟩
      exact (normal_moves ⟨β,γ,σ,r,rfl,rfl,hp,hq⟩).reach

/-- Regular input tuples have regular least Horn extensions. -/
theorem hull_regular (χ : List (Lit n V)) (ρ : V → (BFTree n))
    (hr : ∀ x, IsRegularTree (ρ x)) (y : V) :
    IsRegularTree (assignmentOf (Hull χ (configSet ρ))
      (hull_closed _).prefixClosed y) := by
  change Reg {t | (y,t) ∈ Hull χ (configSet ρ)}
  rw [hull_language]
  apply reg_union (mu_regular χ y)
  have hf := Set.finite_range (fun r => cat {γ | r ∈ Q χ y γ} (seedTail χ ρ r))
  have hg : ∀ L ∈ Set.range (fun r => cat {γ | r ∈ Q χ y γ} (seedTail χ ρ r)), Reg L := by
    rintro L ⟨r,rfl⟩
    exact reg_mul (reg_dfa (lower χ y) {q | r ∈ q}) (seedTail_regular χ ρ hr r)
  simpa only [Set.sUnion_range] using reg_sUnion hf hg

/-- The finite prefix tree naming a singleton seed. -/
def seedTree (a : Config n V) (x : V) : BFTree n where
  K := {w | x = a.1 ∧ w.IsPrefix a.2}
  prefix_closed := by
    rintro u v ⟨hx,hp⟩
    exact ⟨hx, (List.prefix_append u v).trans hp⟩

omit [Fintype V] [DecidableEq V] in
/-- The prefix tree of a single configuration is finite. -/
theorem seedTree_finite (a : Config n V) (x : V) : IsFiniteTree (seedTree a x) :=
  (List.finite_length_le (Fin n) a.2.length).subset (fun _ h => h.2.length_le)

omit [Fintype V] [DecidableEq V] in
/-- Closing a seed prefix tree gives the singleton Horn closure. -/
theorem hull_seedTree (χ : List (Lit n V)) (a : Config n V) :
    Hull χ (configSet (seedTree a)) = Cl χ a := by
  apply Set.Subset.antisymm
  · apply (hull_least _).2.2 _ (cl_closed a)
    rintro b (hb | hb)
    · exact Or.inl (facts_subset_mu hb)
    · obtain ⟨hx,hp⟩ := hb
      obtain ⟨v,hv⟩ := hp
      right
      have h := reach_truncate (χ := χ) a.1 b.2 v
      change Reach χ (a.1,a.2) (b.1,b.2)
      rw [hx]
      simpa only [hv] using h
  · intro b hb
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr ⟨a, ⟨rfl, List.prefix_refl _⟩, hb⟩

/-- Every singleton Horn closure has regular components. -/
theorem cl_regular (χ : List (Lit n V)) (a : Config n V) (y : V) :
    IsRegularTree (assignmentOf (Cl χ a) (cl_closed a).prefixClosed y) := by
  have h := hull_regular χ (seedTree a) (fun x => reg_finite (seedTree_finite a x)) y
  change Reg {w | (y,w) ∈ Hull χ (configSet (seedTree a))} at h
  change Reg {w | (y,w) ∈ Cl χ a}
  simpa only [hull_seedTree] using h

end DeciENSSE.Core.Classes
