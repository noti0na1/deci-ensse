import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import DeciENSSE.Core.Words.NonMortalLasso

/-! # Finite pre-hole automata

A finite two-tape graph recognizes pre-holes with a prescribed set of spine endpoints.
Loop erasure bounds the lengths of accepted words, yielding a finite pre-hole search.

## Main declarations

- `TwoTapeGraph.short_accepts`: bound an accepted pair by the vertex count.
- `TwoWordInstance.preHoleGraph_correct`: characterize accepted pairs.
- `TwoWordInstance.short_preHole`: shorten a pre-hole while retaining its endpoint set.
- `TwoWordInstance.preHoleExistsDecidable`: decide existence by bounded search.
-/

namespace DeciENSSE.Core.Words

variable {α : Type*}

/-- A directed graph whose edges read at most one letter on each tape.
`none` reads no letter, so an edge may be silent on either or both tapes. The graph
itself imposes no alignment condition: `TwoWordInstance.preHoleGraph` uses a phase
in its vertices to enforce right alignment of accepted word pairs. -/
structure TwoTapeGraph (α : Type*) (V : Type*) where
  /-- Labeled directed edges; `none` is a silent tape action. -/
  edge : V → V → Option α → Option α → Prop
  /-- Permitted initial vertices. -/
  initial : V → Prop
  /-- Accepting vertices. -/
  final : V → Prop

namespace TwoTapeGraph
variable {V : Type*} (G : TwoTapeGraph α V)

/-- A finite walk through labeled two-tape edges. -/
inductive Walk (a : V) : V → Type _
  | nil : Walk a a
  | snoc {b c : V} (p : Walk a b) (x y : Option α)
      (h : G.edge b c x y) : Walk a c

namespace Walk
variable {G} {a b c : V}

/-- The visited vertices of a two-tape walk, including both endpoints. -/
def nodes : {b : V} → G.Walk a b → List V
  | _, .nil => [a]
  | b, .snoc p _ _ _ => p.nodes ++ [b]

/-- The word read on the left tape along a walk. -/
def left : {b : V} → G.Walk a b → Word α
  | _, .nil => []
  | _, .snoc p x _ _ => p.left ++ x.toList

/-- The word read on the right tape along a walk. -/
def right : {b : V} → G.Walk a b → Word α
  | _, .nil => []
  | _, .snoc p _ y _ => p.right ++ y.toList

/-- Each tape reads fewer letters than the number of visited vertices. -/
theorem length_bounds (p : G.Walk a b) :
    p.left.length < p.nodes.length ∧ p.right.length < p.nodes.length := by
  induction p with
  | nil => simp [left, right, nodes]
  | snoc p x y h ih =>
    cases x <;> cases y <;> simp_all [left, right, nodes] <;> omega

/-- A visited vertex is the endpoint of a prefix walk. -/
theorem prefix_of_mem (p : G.Walk a b) (hc : c ∈ p.nodes) :
    ∃ q : G.Walk a c, q.nodes.IsPrefix p.nodes := by
  induction p with
  | nil =>
    have : c = a := by simpa [nodes] using hc
    subst c
    exact ⟨.nil, List.prefix_rfl⟩
  | @snoc b d p x y h ih =>
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨q, hq⟩ := ih hc
      exact ⟨q, hq.trans (List.prefix_append _ _)⟩
    · have : c = d := by simpa using hc
      subst c
      exact ⟨.snoc p x y h, List.prefix_rfl⟩

/-- Loop erasure works for directed, labeled edges, including silent edges. -/
theorem exists_simple (p : G.Walk a b) :
    ∃ q : G.Walk a b, q.nodes.Nodup := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp [nodes]⟩
  | @snoc b c p x y h ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hc : c ∈ q.nodes
    · obtain ⟨r, hr⟩ := q.prefix_of_mem hc
      exact ⟨r, hq.sublist hr.sublist⟩
    · refine ⟨.snoc q x y h, ?_⟩
      simp [nodes, List.nodup_append, hq]
      intro v hv he
      exact hc (he ▸ hv)

end Walk

/-- A two-tape graph accepts a pair read by an initial-to-final walk. -/
def Accepts (u t : Word α) : Prop :=
  ∃ a b, G.initial a ∧ G.final b ∧
    ∃ p : G.Walk a b, p.left = u ∧ p.right = t

/-- If some pair is accepted, a pair with both words shorter than the vertex count is accepted. -/
theorem short_accepts [Fintype V] {u t : Word α} (h : G.Accepts u t) :
    ∃ v w, G.Accepts v w ∧ v.length < Fintype.card V ∧ w.length < Fintype.card V := by
  classical
  obtain ⟨a, b, ha, hb, p, _, _⟩ := h
  obtain ⟨q, hq⟩ := p.exists_simple
  have hcard : q.nodes.length ≤ Fintype.card V := by
    simpa using List.Nodup.length_le_card hq
  exact ⟨q.left, q.right, ⟨a, b, ha, hb, q, rfl, rfl⟩,
    lt_of_lt_of_le q.length_bounds.1 hcard,
    lt_of_lt_of_le q.length_bounds.2 hcard⟩

end TwoTapeGraph

namespace TwoWordInstance

/-- Aligned cuts carrying an arbitrary relation on a pair of automata. -/
def AlignedHit {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) (u t : Word α) : Prop :=
  ∃ s ≤ u.length, ∃ e ≤ t.length,
    u.drop s = t.drop e ∧ R (M.atCut u s) (N.atCut t e)

/-- Existence of a related aligned pair is decidable on finite words. -/
instance [DecidableEq α] {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) [DecidableRel R] (u t : Word α) :
    Decidable (AlignedHit M N R u t) := by
  unfold AlignedHit
  infer_instance

/-- Only the terminal cuts can be aligned when the target is empty. -/
theorem alignedHit_nil_right {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) (u : Word α) :
    AlignedHit M N R u [] ↔ R (M.run u) N.start := by
  simp only [AlignedHit, List.length_nil, Nat.le_zero, exists_eq_left,
    List.drop_nil, List.drop_eq_nil_iff, LDFA.atCut, List.take_nil,
    LDFA.run, LDFA.runFrom_nil]
  constructor
  · rintro ⟨s, hs, he, hr⟩
    have : s = u.length := by omega
    simpa [this] using hr
  · intro h
    exact ⟨u.length, le_rfl, le_rfl, by simpa using h⟩

/-- Only the terminal cuts can be aligned when the spine is empty. -/
theorem alignedHit_nil_left {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) (t : Word α) :
    AlignedHit M N R [] t ↔ R M.start (N.run t) := by
  have hswap : AlignedHit M N R [] t ↔ AlignedHit N M (fun b a => R a b) t [] := by
    constructor <;> rintro ⟨s, hs, e, he, hd, hr⟩
    · exact ⟨e, he, s, hs, hd.symm, hr⟩
    · exact ⟨e, he, s, hs, hd.symm, hr⟩
  exact hswap.trans (alignedHit_nil_right N M _ t)

/-- Equal last letters preserve old aligned hits; unequal letters reset them. -/
theorem alignedHit_snoc {S T : Type*} (M : LDFA α S) (N : LDFA α T)
    (R : S → T → Prop) (u t : Word α) (c d : α) :
    AlignedHit M N R (u ++ [c]) (t ++ [d]) ↔
      R (M.run (u ++ [c])) (N.run (t ++ [d])) ∨
        (c = d ∧ AlignedHit M N R u t) := by
  constructor
  · rintro ⟨s, hs, e, he, hd, hr⟩
    have hlen := congrArg List.length hd
    simp only [List.length_drop, List.length_append, List.length_singleton] at hs he hlen
    by_cases hsu : s ≤ u.length
    · have het : e ≤ t.length := by omega
      rw [List.drop_append_of_le_length hsu, List.drop_append_of_le_length het] at hd
      have hlast : c = d := by
        have hh := congrArg List.getLast? hd
        simpa using hh
      subst d
      have hdrop := List.append_cancel_right hd
      exact Or.inr ⟨rfl, s, hsu, e, het, hdrop,
        by simpa [LDFA.atCut_append _ _ _ hsu,
          LDFA.atCut_append _ _ _ het] using hr⟩
    · have hse : s = (u ++ [c]).length := by simp; omega
      have hee : e = (t ++ [d]).length := by simp; omega
      exact Or.inl (by simpa only [hse, hee, LDFA.atCut, List.take_length] using hr)
  · rintro (h | ⟨rfl, s, hs, e, he, hd, hr⟩)
    · exact ⟨_, le_rfl, _, le_rfl, by simp, by simpa only [LDFA.atCut, List.take_length] using h⟩
    · exact ⟨s, by simp; omega, e, by simp; omega,
        by simp [List.drop_append_of_le_length hs, List.drop_append_of_le_length he, hd],
        by simpa [LDFA.atCut_append _ _ _ hs,
          LDFA.atCut_append _ _ _ he] using hr⟩

/-- Four reader states, head/guard bits, and a phase: 0 = spine prefix,
1 = target prefix, 2 = synchronous suffix. -/
structure PreNode (SA SB SA' SB' : Type*) where
  a : SA
  b : SB
  a' : SA'
  b' : SB'
  hd : Bool
  gd : Bool
  phase : Fin 3
  deriving DecidableEq

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')

/-- The target has not rejected at any proper cut. -/
def TargetOpen (t : Word α) : Prop := ∀ i < t.length, I.B.atCut t i ∉ I.Rej

/-- It is decidable whether every proper target prefix is unrejected. -/
instance (t : Word α) : Decidable (I.TargetOpen t) := by
  unfold TargetOpen
  infer_instance

/-- Appending one letter updates whether the target remains unrejected. -/
theorem targetOpen_snoc (t : Word α) (d : α) :
    I.TargetOpen (t ++ [d]) ↔ I.TargetOpen t ∧ I.B.run t ∉ I.Rej := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [LDFA.atCut_append _ _ _ (by omega : i ≤ t.length)] using
        h i (by simp; omega)
    · simpa [LDFA.atCut, List.take_append] using h t.length (by simp)
  · rintro ⟨h, he⟩ i hi
    have hil : i ≤ t.length := by simp at hi; omega
    rw [LDFA.atCut_append _ _ _ hil]
    rcases lt_or_eq_of_le hil with hi | rfl
    · exact h i hi
    · simpa [LDFA.atCut] using he

/-- Appending one letter preserves safety exactly when the new state is nonbad. -/
theorem safe_snoc (u : Word α) (c : α) :
    I.SafeFrom I.A.start (u ++ [c]) ↔
      I.SafeFrom I.A.start u ∧ I.A.step (I.A.run u) c ∉ I.Bad := by
  rw [I.safeFrom_append, I.safeFrom_cons]
  constructor
  · rintro ⟨hu, _, hc⟩
    exact ⟨hu, I.safeFrom_start hc⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, I.safeFrom_end hu, by simpa [SafeFrom, LDFA.run] using hc⟩

/-- Pre-holes are characterized by safety, rejection, and the aligned-pair flags. -/
theorem preHole_iff_alignedHit (u t : Word α) :
    I.IsPreHole u t ↔ I.SafeFrom I.A.start u ∧ I.TargetOpen t ∧
      I.B.run t ∈ I.Rej ∧
      AlignedHit I.A' I.B' (fun a b => (a,b) ∈ I.Head) u t ∧
      ¬ AlignedHit I.A I.B (fun a b => (a,b) ∈ I.Guard) u t := by
  have hj : I.J t = some t.length ↔ I.B.run t ∈ I.Rej ∧ I.TargetOpen t := by
    simpa [LDFA.atCut, TargetOpen] using I.J_eq_some_iff t t.length
  constructor
  · rintro ⟨hs, hrej, hh, hg⟩
    obtain ⟨s, _, e, _, ha, hr⟩ := hh
    refine ⟨hs, (hj.mp hrej).2, (hj.mp hrej).1,
      ⟨s, ha.1, e, ha.2.1, ha.2.2, hr⟩, ?_⟩
    rintro ⟨s, hs, e, he, hd, hr⟩
    exact hg s (Finset.mem_range.mpr (by omega)) e (Finset.mem_range.mpr (by omega))
      ⟨⟨⟨hs, he, hd ▸ List.prefix_rfl⟩, ⟨t.length, by simp [hrej], he⟩, hr⟩,
        hs, he, hd⟩
  · rintro ⟨hs, ht, hr, ⟨s, hs', e, he, hd, hh⟩, hg⟩
    refine ⟨hs, hj.mpr ⟨hr, ht⟩,
      ⟨s, Finset.mem_range.mpr (by omega), e, Finset.mem_range.mpr (by omega),
        ⟨hs', he, hd⟩, hh⟩, ?_⟩
    intro s _ e _ h
    exact hg ⟨s, h.2.1, e, h.2.2.1, h.2.2.2, h.1.2.2⟩

/-- Product presentation, also furnishing the executable enumeration of nodes. -/
def preNodeEquiv : PreNode SA SB SA' SB' ≃ SA × SB × SA' × SB' × Bool × Bool × Fin 3 :=
  { toFun := fun p => (p.a, p.b, p.a', p.b', p.hd, p.gd, p.phase)
    invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1,
      p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
    left_inv := fun p => by cases p; rfl
    right_inv := fun p => rfl }

/-- The pre-hole node type is finite. -/
instance : Fintype (PreNode SA SB SA' SB') :=
  Fintype.ofEquiv (SA × SB × SA' × SB' × Bool × Bool × Fin 3) preNodeEquiv.symm

omit [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB'] in
/-- Exact cardinality of the forward pre-hole automaton. -/
theorem card_preNode : Fintype.card (PreNode SA SB SA' SB') =
    12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB' := by
  rw [Fintype.card_congr (preNodeEquiv (SA := SA) (SB := SB) (SA' := SA') (SB' := SB'))]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

variable [DecidableEq α]

/-- The graph node records four reader states and the aligned-pair flags. -/
def preNode (u t : Word α) (phase : Fin 3) : PreNode SA SB SA' SB' :=
  ⟨I.A.run u, I.B.run t, I.A'.run u, I.B'.run t,
    decide (AlignedHit I.A' I.B' (fun a b => (a,b) ∈ I.Head) u t),
    decide (AlignedHit I.A I.B (fun a b => (a,b) ∈ I.Guard) u t), phase⟩

/-- A left-only transition updates the spine readers. -/
def preLeft (p : PreNode SA SB SA' SB') (c : α) : PreNode SA SB SA' SB' :=
  let a := I.A.step p.a c
  let a' := I.A'.step p.a' c
  ⟨a, p.b, a', p.b', decide ((a', p.b') ∈ I.Head),
    decide ((a, p.b) ∈ I.Guard), 0⟩

/-- A right-only transition updates the target readers. -/
def preRight (p : PreNode SA SB SA' SB') (d : α) : PreNode SA SB SA' SB' :=
  let b := I.B.step p.b d
  let b' := I.B'.step p.b' d
  ⟨p.a, b, p.a', b', decide ((p.a', b') ∈ I.Head),
    decide ((p.a, b) ∈ I.Guard), 1⟩

/-- A simultaneous transition updates both words and their aligned-pair flags. -/
def preBoth (p : PreNode SA SB SA' SB') (c d : α) : PreNode SA SB SA' SB' :=
  let a := I.A.step p.a c
  let b := I.B.step p.b d
  let a' := I.A'.step p.a' c
  let b' := I.B'.step p.b' d
  ⟨a, b, a', b', decide ((a', b') ∈ I.Head) || (decide (c = d) && p.hd),
    decide ((a, b) ∈ I.Guard) || (decide (c = d) && p.gd), 2⟩

omit [DecidableEq α] in
/-- A run on a word with one appended letter takes one final transition. -/
theorem run_snoc {S : Type*} (M : LDFA α S) (u : Word α) (c : α) :
    M.run (u ++ [c]) = M.step (M.run u) c := by
  simp [LDFA.run, LDFA.runFrom, List.foldl_append]

/-- A left-only transition agrees with the node of the extended word pair. -/
theorem preLeft_node (u : Word α) (c : α) (phase : Fin 3) :
    I.preLeft (I.preNode u [] phase) c = I.preNode (u ++ [c]) [] 0 := by
  simp [preLeft, preNode, alignedHit_nil_right, LDFA.run, LDFA.runFrom, List.foldl_append]

/-- A right-only transition agrees with the node of the extended word pair. -/
theorem preRight_node (t : Word α) (d : α) (phase : Fin 3) :
    I.preRight (I.preNode [] t phase) d = I.preNode [] (t ++ [d]) 1 := by
  simp [preRight, preNode, alignedHit_nil_left, LDFA.run, LDFA.runFrom, List.foldl_append]

/-- A simultaneous transition agrees with the node of the extended word pair. -/
theorem preBoth_node (u t : Word α) (c d : α) (phase : Fin 3) :
    I.preBoth (I.preNode u t phase) c d = I.preNode (u ++ [c]) (t ++ [d]) 2 := by
  simp [preBoth, preNode, alignedHit_snoc, run_snoc]
  constructor <;> rfl

/-- A computable two-tape graph recognizing pre-holes with endpoint in `E`.
Only one tape may run ahead initially; thereafter both tapes move together. -/
def preHoleGraph (E : Finset SA) : TwoTapeGraph α (PreNode SA SB SA' SB') where
  edge p q x y := match x, y with
    | some c, none => p.phase = 0 ∧ q = I.preLeft p c ∧ q.a ∉ I.Bad
    | none, some d => p.phase = 1 ∧ q = I.preRight p d ∧ p.b ∉ I.Rej
    | some c, some d => q = I.preBoth p c d ∧ q.a ∉ I.Bad ∧ p.b ∉ I.Rej
    | none, none => False
  initial p := p = I.preNode [] [] p.phase ∧ I.A.start ∉ I.Bad
  final p := p.a ∈ E ∧ p.b ∈ I.Rej ∧ p.hd = true ∧ p.gd = false

/-- Pre-hole graph edges are decidable. -/
instance (E : Finset SA) (p q : PreNode SA SB SA' SB') (x y : Option α) :
    Decidable ((I.preHoleGraph E).edge p q x y) := by
  unfold preHoleGraph
  cases x <;> cases y <;> dsimp <;> infer_instance

/-- Initial nodes of the pre-hole graph are decidable. -/
instance (E : Finset SA) (p : PreNode SA SB SA' SB') :
    Decidable ((I.preHoleGraph E).initial p) := by
  unfold preHoleGraph
  infer_instance

/-- Final nodes of the pre-hole graph are decidable. -/
instance (E : Finset SA) (p : PreNode SA SB SA' SB') :
    Decidable ((I.preHoleGraph E).final p) := by
  unfold preHoleGraph
  infer_instance

/-- Semantic invariant for a node after reading a pair of prefixes. -/
def PreValid (p : PreNode SA SB SA' SB') (u t : Word α) : Prop :=
  ∃ phase, p = I.preNode u t phase ∧ I.SafeFrom I.A.start u ∧ I.TargetOpen t ∧
    (phase = 0 → t = []) ∧ (phase = 1 → u = [])

/-- A graph transition preserves the validity of its node. -/
theorem preValid_step (E : Finset SA) {p q : PreNode SA SB SA' SB'}
    {u t : Word α} {x y : Option α} (hp : I.PreValid p u t)
    (he : (I.preHoleGraph E).edge p q x y) :
    I.PreValid q (u ++ x.toList) (t ++ y.toList) := by
  obtain ⟨phase, rfl, hu, ht, hzero, hone⟩ := hp
  cases x with
  | none =>
    cases y with
    | none => exact he.elim
    | some d =>
      obtain ⟨hphase, rfl, hb⟩ := he
      have hue : u = [] := hone hphase
      subst u
      simp only [Option.toList_none, Option.toList_some, List.append_nil]
      refine ⟨1, I.preRight_node t d phase, hu,
        (I.targetOpen_snoc t d).mpr ⟨ht, hb⟩, ?_, fun _ => rfl⟩
      intro h
      exact (by decide : (1 : Fin 3) ≠ 0) h |>.elim
  | some c =>
    cases y with
    | none =>
      obtain ⟨hphase, rfl, ha⟩ := he
      have hte : t = [] := hzero hphase
      subst t
      simp only [Option.toList_none, Option.toList_some, List.append_nil]
      refine ⟨0, I.preLeft_node u c phase, (I.safe_snoc u c).mpr ⟨hu, ha⟩,
        ht, fun _ => rfl, ?_⟩
      intro h
      exact (by decide : (0 : Fin 3) ≠ 1) h |>.elim
    | some d =>
      obtain ⟨rfl, ha, hb⟩ := he
      refine ⟨2, I.preBoth_node u t c d phase, (I.safe_snoc u c).mpr ⟨hu, ha⟩,
        (I.targetOpen_snoc t d).mpr ⟨ht, hb⟩, ?_, ?_⟩
      · intro h
        exact (by decide : (2 : Fin 3) ≠ 0) h |>.elim
      · intro h
        exact (by decide : (2 : Fin 3) ≠ 1) h |>.elim

/-- A graph walk preserves the validity of its node. -/
theorem preValid_walk (E : Finset SA) {a b : PreNode SA SB SA' SB'}
    (p : (I.preHoleGraph E).Walk a b) (ha : (I.preHoleGraph E).initial a) :
    I.PreValid b p.left p.right := by
  induction p with
  | nil =>
    exact ⟨a.phase, ha.1, by simpa [SafeFrom, TwoTapeGraph.Walk.left] using ha.2,
      by simp [TargetOpen, TwoTapeGraph.Walk.right], fun _ => rfl, fun _ => rfl⟩
  | snoc p x y h ih => exact I.preValid_step E ih h

/-- Soundness of the pre-hole graph. -/
theorem preHoleGraph_sound (E : Finset SA) {u t : Word α}
    (h : (I.preHoleGraph E).Accepts u t) : I.IsPreHole u t ∧ I.A.run u ∈ E := by
  obtain ⟨a, b, ha, hb, p, rfl, rfl⟩ := h
  obtain ⟨phase, heq, hu, ht, _, _⟩ := I.preValid_walk E p ha
  rw [heq] at hb
  have hf : I.A.run p.left ∈ E ∧ I.B.run p.right ∈ I.Rej ∧
      AlignedHit I.A' I.B' (fun a b => (a,b) ∈ I.Head) p.left p.right ∧
      ¬ AlignedHit I.A I.B (fun a b => (a,b) ∈ I.Guard) p.left p.right := by
    exact ⟨hb.1, hb.2.1, of_decide_eq_true hb.2.2.1, of_decide_eq_false hb.2.2.2⟩
  exact ⟨(I.preHole_iff_alignedHit _ _).mpr ⟨hu, ht, hf.2⟩, hf.1⟩

/-- The initial spine-only phase reads any safe spine. -/
theorem preHoleGraph_leftWalk (E : Finset SA) {u : Word α}
    (hu : I.SafeFrom I.A.start u) :
    ∃ p : (I.preHoleGraph E).Walk (I.preNode [] [] 0) (I.preNode u [] 0),
      p.left = u ∧ p.right = [] := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | append_singleton u c ih =>
    obtain ⟨hs, hc⟩ := (I.safe_snoc u c).mp hu
    obtain ⟨p, hp, ht⟩ := ih hs
    have he : (I.preHoleGraph E).edge (I.preNode u [] 0)
        (I.preNode (u ++ [c]) [] 0) (some c) none :=
      ⟨rfl, (I.preLeft_node u c 0).symm, by simpa only [preNode, run_snoc] using hc⟩
    exact ⟨p.snoc _ _ he, by simp [TwoTapeGraph.Walk.left, hp],
      by simp [TwoTapeGraph.Walk.right, ht]⟩

/-- The initial target-only phase reads any target with no proper rejection. -/
theorem preHoleGraph_rightWalk (E : Finset SA) {t : Word α} (ht : I.TargetOpen t) :
    ∃ p : (I.preHoleGraph E).Walk (I.preNode [] [] 1) (I.preNode [] t 1),
      p.left = [] ∧ p.right = t := by
  induction t using List.reverseRecOn with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | append_singleton t d ih =>
    obtain ⟨hs, hd⟩ := (I.targetOpen_snoc t d).mp ht
    obtain ⟨p, hp, ht⟩ := ih hs
    have he : (I.preHoleGraph E).edge (I.preNode [] t 1)
        (I.preNode [] (t ++ [d]) 1) none (some d) :=
      ⟨rfl, (I.preRight_node t d 1).symm, hd⟩
    exact ⟨p.snoc _ _ he, by simp [TwoTapeGraph.Walk.left, hp],
      by simp [TwoTapeGraph.Walk.right, ht]⟩

/-- Every safe pair with no proper target rejection has its canonical
right-aligned convolution run. -/
theorem preHoleGraph_run (E : Finset SA) {u t : Word α}
    (hu : I.SafeFrom I.A.start u) (ht : I.TargetOpen t) :
    ∃ a phase, (I.preHoleGraph E).initial a ∧
      ∃ p : (I.preHoleGraph E).Walk a (I.preNode u t phase),
        p.left = u ∧ p.right = t := by
  induction u using List.reverseRecOn generalizing t with
  | nil =>
    obtain ⟨p, hp⟩ := I.preHoleGraph_rightWalk E ht
    exact ⟨_, 1, ⟨rfl, I.safeFrom_start hu⟩, p, hp⟩
  | append_singleton u c ih =>
    induction t using List.reverseRecOn with
    | nil =>
      obtain ⟨p, hp⟩ := I.preHoleGraph_leftWalk E hu
      exact ⟨_, 0, ⟨rfl, I.safeFrom_start hu⟩, p, hp⟩
    | append_singleton t d _ =>
      obtain ⟨hus, hc⟩ := (I.safe_snoc u c).mp hu
      obtain ⟨hts, hd⟩ := (I.targetOpen_snoc t d).mp ht
      obtain ⟨a, phase, ha, p, hp, hq⟩ := ih hus hts
      have he : (I.preHoleGraph E).edge (I.preNode u t phase)
          (I.preNode (u ++ [c]) (t ++ [d]) 2) (some c) (some d) :=
        ⟨(I.preBoth_node u t c d phase).symm,
          by simpa only [preNode, run_snoc] using hc, hd⟩
      exact ⟨a, 2, ha, p.snoc _ _ he,
        by simp [TwoTapeGraph.Walk.left, hp], by simp [TwoTapeGraph.Walk.right, hq]⟩

/-- Completeness of the pre-hole graph. -/
theorem preHoleGraph_complete (E : Finset SA) {u t : Word α}
    (hp : I.IsPreHole u t) (he : I.A.run u ∈ E) : (I.preHoleGraph E).Accepts u t := by
  obtain ⟨hu, ht, hr, hh, hg⟩ := (I.preHole_iff_alignedHit u t).mp hp
  obtain ⟨a, phase, ha, p, hp, hq⟩ := I.preHoleGraph_run E hu ht
  refine ⟨a, I.preNode u t phase, ha, ?_, p, hp, hq⟩
  simpa [preHoleGraph, preNode] using And.intro he ⟨hr, hh, hg⟩

/-- The graph recognizes exactly the pre-holes with endpoint in the chosen set. -/
theorem preHoleGraph_correct (E : Finset SA) (u t : Word α) :
    (I.preHoleGraph E).Accepts u t ↔ I.IsPreHole u t ∧ I.A.run u ∈ E :=
  ⟨I.preHoleGraph_sound E, fun h => I.preHoleGraph_complete E h.1 h.2⟩

/-- Pre-hole witnesses are shorter than twelve times the four-state product. -/
theorem short_preHole (E : Finset SA) {u t : Word α}
    (hp : I.IsPreHole u t) (he : I.A.run u ∈ E) :
    ∃ v w, I.IsPreHole v w ∧ I.A.run v ∈ E ∧
      v.length < 12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB' ∧
      w.length < 12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB' := by
  obtain ⟨v, w, hv, hl, hr⟩ := (I.preHoleGraph E).short_accepts
    (I.preHoleGraph_complete E hp he)
  obtain ⟨hp, he⟩ := I.preHoleGraph_sound E hv
  exact ⟨v, w, hp, he, by simpa only [card_preNode] using hl,
    by simpa only [card_preNode] using hr⟩

/-- Executable emptiness test for P_E, using the proved finite bound. -/
def preHoleExistsDecidable [Fintype α] (E : Finset SA) :
    Decidable (∃ u t, I.IsPreHole u t ∧ I.A.run u ∈ E) := by
  let K := 12 * Fintype.card SA * Fintype.card SB * Fintype.card SA' * Fintype.card SB'
  letI (u : Word α) :
      Decidable (∃ t ∈ wordsUpTo K, I.IsPreHole u t ∧ I.A.run u ∈ E) :=
    Finset.decidableExistsAndFinset (s := wordsUpTo K)
      (p := fun t : Word α => I.IsPreHole u t ∧ I.A.run u ∈ E)
  letI : Decidable
      (∃ u ∈ wordsUpTo K, ∃ t ∈ wordsUpTo K, I.IsPreHole u t ∧ I.A.run u ∈ E) :=
    Finset.decidableExistsAndFinset (s := wordsUpTo K)
      (p := fun u : Word α => ∃ t ∈ wordsUpTo K, I.IsPreHole u t ∧ I.A.run u ∈ E)
  exact decidable_of_iff
    (∃ u ∈ wordsUpTo K, ∃ t ∈ wordsUpTo K, I.IsPreHole u t ∧ I.A.run u ∈ E)
    (by
      constructor
      · rintro ⟨u, _, t, _, hp⟩
        exact ⟨u, t, hp⟩
      · rintro ⟨u, t, hp, he⟩
        obtain ⟨v, w, hp, he, hv, hw⟩ := I.short_preHole E hp he
        exact ⟨v, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hv),
          w, (mem_wordsUpTo _ _).mpr (Nat.le_of_lt hw), hp, he⟩)

end TwoWordInstance

end DeciENSSE.Core.Words
