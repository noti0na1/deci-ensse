import DeciENSSE.Core.Words.Mortal.SepWord
import DeciNSSE.Holes.Hierarchy.Reader
import DeciNSSE.RejectedTail.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-! # The mortal Π-reader

The Π-reader of an instance reads separator words. Before the separator it runs the spine
automaton and its head automaton and falls into a sink at an unsafe state. At the separator
it continues only from a mortal spine state, then runs the target automaton and its head
automaton up to the first rejected cut and counts the letters after it, rejecting while
fewer than `|SA|` letters follow. Admissions join spine states to active target states
through the guard, and `Pi` joins spine head states to target head states through the head
relation. The holes of this reader with an anchored comparison in `Pi` are exactly the
separator words of the mortal holes of the instance.

The counter value `k : Fin |SA|` stands for `k + 1` letters after the first rejected cut,
saturated at `|SA|`. All states of the product types are kept, reachable or not, so
`card_state` is an exact count.

## Main declarations

- `RState`, `reader`, `Adm`, `Rej`, `Pi`: the states, the reader, its admissions, its
  rejected states, and the anchored relation.
- `card_state`: the number of states.
- `HasPi`, `PiHole`: an anchored comparison in `Pi`, and holes with one.
- `rejected_sep_iff`, `first_rejected_cut`: rejection and the first rejected cut on
  separator words.
- `piHole_sep_iff`, `piReader_iff`, `ofReader_pi_iff`: the Π-holes are the separator words
  of mortal holes.
- `rejected_word_form`, `rejected_count_separator`: rejected words have one separator.

The declarations are in the namespace `DeciENSSE.Core.Words.Mortal`.
-/

namespace DeciENSSE.Core.Words.Mortal

variable {α : Type*} [Fintype α] [DecidableEq α]
open DeciNSSE.CoAlignment DeciNSSE.Holes DeciNSSE.RejectedTail

/-- States of the Π-reader: before the separator, active on the target, after the first
rejected cut with a counter, and a sink. -/
inductive RState (SA SB SA' SB' : Type*) [Fintype SA] where
  | pre (a : SA) (a' : SA')
  | act (b : SB) (b' : SB')
  | done (b' : SB') (k : Fin (Fintype.card SA))
  | sink
  deriving DecidableEq, Fintype

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')

/-- The states of the Π-reader of `I`. -/
abbrev State := RState SA SB SA' SB'

omit [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB'] in
/-- The number of states of the Π-reader. -/
theorem card_state : Fintype.card (State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) =
    1 + Fintype.card SA * Fintype.card SA' + Fintype.card SB * Fintype.card SB' +
      Fintype.card SA * Fintype.card SB' := by
  let e : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') ≃
      Option ((SA × SA') ⊕ (SB × SB') ⊕ (SB' × Fin (Fintype.card SA))) :=
    { toFun := fun q => match q with
        | .pre a a' => some (.inl (a,a'))
        | .act b b' => some (.inr (.inl (b,b')))
        | .done b' k => some (.inr (.inr (b',k)))
        | .sink => none
      invFun := fun q => match q with
        | some (.inl (a,a')) => .pre a a'
        | some (.inr (.inl (b,b'))) => .act b b'
        | some (.inr (.inr (b',k))) => .done b' k
        | none => .sink
      left_inv := by intro q; cases q <;> rfl
      right_inv := by rintro (_ | (⟨a,a'⟩ | (⟨b,b'⟩ | ⟨b',k⟩))) <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

include I in
omit [Fintype α] [DecidableEq α] in
/-- The spine automaton has a state. -/
theorem card_A_pos : 0 < Fintype.card SA := Fintype.card_pos_iff.mpr ⟨I.A.start⟩

/-- The saturated counter of letters after the first rejected cut. -/
def counter (n : ℕ) : Fin (Fintype.card SA) :=
  ⟨min n (Fintype.card SA - 1), by have := card_A_pos I; omega⟩

omit [Fintype α] [DecidableEq α] in
/-- The value of the counter. -/
@[simp] theorem counter_val (n : ℕ) : (counter I n).val = min n (Fintype.card SA - 1) := rfl

omit [Fintype α] [DecidableEq α] in
/-- Incrementing the counter. -/
@[simp] theorem counter_succ (n : ℕ) : counter I ((counter I n).val + 1) = counter I (n+1) := by
  apply Fin.ext
  simp only [counter_val]
  omega

/-- The Π-reader. -/
def reader : DFA (Option α) (State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) where
  start := if I.A.start ∈ I.Bad then .sink else .pre I.A.start I.A'.start
  step q c := match q, c with
    | .pre a a', some c => if I.A.step a c ∈ I.Bad then .sink
        else .pre (I.A.step a c) (I.A'.step a' c)
    | .pre a _, none => if I.Mortal a then .act I.B.start I.B'.start else .sink
    | .act b b', some c => if b ∈ I.Rej then .done (I.B'.step b' c) (counter I 0)
        else .act (I.B.step b c) (I.B'.step b' c)
    | .done b' k, some c => .done (I.B'.step b' c) (counter I (k.val+1))
    | _, _ => .sink
  accept := ∅

/-- Admissions join a spine state and an active target state in the guard. -/
def Adm : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') →
    State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') → Prop
  | .pre a _, .act b _ => (a,b) ∈ I.Guard
  | _, _ => False

/-- Rejected states: an active rejected target state, or fewer than `|SA|` letters after the
first rejected cut. -/
def Rej : Set (State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB'))
  | .act b _ => b ∈ I.Rej
  | .done _ k => k.val + 1 < Fintype.card SA
  | _ => False

/-- The anchored relation joins a spine head state and a target head state in the head
relation. -/
def Pi : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') →
    State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') → Prop
  | .pre _ a', .act _ b' => (a',b') ∈ I.Head
  | .pre _ a', .done b' _ => (a',b') ∈ I.Head
  | _, _ => False

/-- Admissions are decidable. -/
instance instDecidableAdm : DecidableRel (Adm I) := by
  intro p q; cases p <;> cases q <;> unfold Adm <;> infer_instance
/-- Rejection is decidable. -/
instance instDecidableRej : DecidablePred (· ∈ Rej I) := by
  intro q
  change Decidable (Rej I q)
  cases q <;> dsimp [Rej] <;> infer_instance
/-- The anchored relation is decidable. -/
instance instDecidablePi : DecidableRel (Pi I) := by
  intro p q; cases p <;> cases q <;> unfold Pi <;> infer_instance

/-- The word has one separator and an anchored comparison at it in `Pi`. -/
def HasPi (w : List (Option α)) : Prop :=
  ∃ p, w.count none = 1 ∧ w[p]? = some none ∧
    ∃ s e, Anchored w p s e ∧ Pi I (runPrefix (reader I) w s) (runPrefix (reader I) w e)

/-- A Π-hole: a reader hole with an anchored comparison in `Pi`. -/
def PiHole (w : List (Option α)) : Prop :=
  IsReaderHole (reader I) (Adm I) (Rej I) w ∧ HasPi I w

omit [DecidableEq α] in
/-- The sink is absorbing. -/
@[simp] theorem eval_sink (v : List (Option α)) :
    (reader I).evalFrom .sink v = .sink := by
  induction v with
  | nil => rfl
  | cons c v ih => simpa [DFA.evalFrom_cons, reader] using ih

omit [Fintype α] [DecidableEq α] in
/-- The run after appending a letter. -/
@[simp] theorem run_snoc {S : Type*} (M : LDFA α S) (v : Word α) (c : α) :
    M.run (v ++ [c]) = M.step (M.run v) c := by
  simp [LDFA.run, LDFA.runFrom, List.foldl_append]

omit [Fintype α] [DecidableEq α] in
/-- Safety of a spine extended by one letter. -/
theorem safe_snoc (u : Word α) (c : α) :
    I.SafeFrom I.A.start (u ++ [c]) ↔
      I.SafeFrom I.A.start u ∧ I.A.run (u ++ [c]) ∉ I.Bad := by
  simp only [TwoWordInstance.SafeFrom, Finset.mem_range]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa [List.take_append_of_le_length (by omega : i ≤ u.length)] using
        h i (by simp; omega)
    · simpa only [List.take_length, LDFA.run] using h (u ++ [c]).length (by omega)
  · rintro ⟨h,hend⟩ i hi
    by_cases hle : i ≤ u.length
    · simpa [List.take_append_of_le_length hle] using h i (by omega)
    · have he : i = (u ++ [c]).length := by simp at hi ⊢; omega
      rw [he, List.take_length]
      exact hend

omit [DecidableEq α] in
/-- Before the separator, the reader runs the spine and its head automaton, or sinks. -/
theorem eval_binary (u : Word α) : (reader I).eval (u.map some) =
    if I.SafeFrom I.A.start u then .pre (I.A.run u) (I.A'.run u) else .sink := by
  induction u using List.reverseRecOn with
  | nil => simp [TwoWordInstance.SafeFrom, LDFA.run, reader, DFA.eval]
  | append_singleton u c ih =>
    simp only [List.map_append, List.map_singleton, DFA.eval_append_singleton, ih]
    simp only [safe_snoc]
    by_cases h : I.SafeFrom I.A.start u
    · simp [h, reader, run_snoc]
    · simp [h, reader]

omit [DecidableEq α] in
/-- At the separator, the reader becomes active iff the spine is safe and ends mortal. -/
theorem eval_separator (u : Word α) : (reader I).eval (sepWord u []) =
    if I.SafeFrom I.A.start u ∧ I.Mortal (I.A.run u)
    then .act I.B.start I.B'.start else .sink := by
  change (reader I).eval (u.map some ++ [none]) = _
  rw [DFA.eval_append_singleton, eval_binary]
  by_cases hs : I.SafeFrom I.A.start u <;> simp [hs, reader]

omit [DecidableEq α] in
/-- The state after a separator word. -/
theorem eval_sep (u t : Word α) : (reader I).eval (sepWord u t) =
    if I.SafeFrom I.A.start u ∧ I.Mortal (I.A.run u)
    then (reader I).evalFrom (.act I.B.start I.B'.start) (t.map some) else .sink := by
  have he : sepWord u t = sepWord u [] ++ t.map some := by simp [sepWord]
  rw [he]
  change (reader I).evalFrom (reader I).start (_ ++ _) = _
  rw [DFA.evalFrom_of_append]
  change (reader I).evalFrom ((reader I).eval (sepWord u [])) _ = _
  rw [eval_separator]
  split <;> simp_all

omit [DecidableEq α] in
/-- The active phase, up to and including the first rejected cut. -/
theorem eval_active (t : Word α) (h : ∀ i < t.length, I.B.atCut t i ∉ I.Rej) :
    (reader I).evalFrom (.act I.B.start I.B'.start) (t.map some) =
      .act (I.B.run t) (I.B'.run t) := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t c ih =>
    have ht : ∀ i < t.length, I.B.atCut t i ∉ I.Rej := by
      intro i hi
      simpa [LDFA.atCut, List.take_append_of_le_length (by omega : i ≤ t.length)] using
        h i (by simp; omega)
    have hb : I.B.run t ∉ I.Rej := by
      simpa [LDFA.atCut] using h t.length (by simp)
    rw [List.map_append, DFA.evalFrom_of_append, ih ht]
    simp [reader, hb, run_snoc]

omit [DecidableEq α] in
/-- After the first rejected cut, the counter counts letters with saturation. -/
theorem eval_done (b' : SB') (n : ℕ) (t : Word α) :
    (reader I).evalFrom (.done b' (counter I n)) (t.map some) =
      .done (I.B'.runFrom b' t) (counter I (n + t.length)) := by
  induction t generalizing b' n with
  | nil => simp
  | cons c t ih =>
    simp only [List.map_cons, DFA.evalFrom_cons]
    change (reader I).evalFrom (.done (I.B'.step b' c) (counter I ((counter I n).val+1))) _ = _
    rw [counter_succ, ih]
    simp [LDFA.runFrom, List.foldl_cons, Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq α] in
/-- Leaving a rejected active state starts the counter. -/
theorem eval_after (b : SB) (b' : SB') (t : Word α) (ht : t ≠ []) (hb : b ∈ I.Rej) :
    (reader I).evalFrom (.act b b') (t.map some) =
      .done (I.B'.runFrom b' t) (counter I (t.length - 1)) := by
  cases t with
  | nil => contradiction
  | cons c t =>
    simp only [List.map_cons, DFA.evalFrom_cons]
    change (reader I).evalFrom (if b ∈ I.Rej then _ else _) _ = _
    rw [ite_eq_left hb, eval_done]
    simp [LDFA.runFrom, List.foldl_cons]

omit [DecidableEq α] in
/-- The state at every cut of the target; the target head state is kept after the first
rejected cut. -/
theorem eval_target_cut (t : Word α) {j e : ℕ} (hj : I.J t = some j) (he : e ≤ t.length) :
    (reader I).evalFrom (.act I.B.start I.B'.start) ((t.take e).map some) =
      if e ≤ j then .act (I.B.atCut t e) (I.B'.atCut t e)
      else .done (I.B'.atCut t e) (counter I (e-j-1)) := by
  have hJ := (I.J_eq_some_iff t j).mp hj
  have hactive (k : ℕ) (hk : k ≤ j) :
      (reader I).evalFrom (.act I.B.start I.B'.start) ((t.take k).map some) =
        .act (I.B.atCut t k) (I.B'.atCut t k) := by
    apply eval_active
    intro i hi
    have hi' : i < k := by simp only [List.length_take] at hi; omega
    simpa [LDFA.atCut, List.take_take, Nat.min_eq_left (by omega : i ≤ k)] using
      hJ.2.2 i (by omega)
  by_cases hle : e ≤ j
  · rw [ite_eq_left hle]; exact hactive e hle
  · rw [ite_eq_right hle]
    have hjle : j ≤ e := by omega
    have hs : t.take e = t.take j ++ (t.take e).drop j := by
      simpa [List.take_take, Nat.min_eq_left hjle] using
        (List.take_append_drop j (t.take e)).symm
    have hne : (t.take e).drop j ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp only [List.length_drop, List.length_take, Nat.min_eq_left he]
      omega
    conv_lhs => rw [hs, List.map_append, DFA.evalFrom_of_append, hactive j le_rfl]
    rw [eval_after I _ _ _ hne hJ.1]
    have hrun : I.B'.runFrom (I.B'.atCut t j) ((t.take e).drop j) = I.B'.atCut t e := by
      change I.B'.runFrom (I.B'.runFrom I.B'.start (t.take j)) _ = _
      rw [← LDFA.runFrom_append, ← hs]
      rfl
    rw [hrun]
    simp only [List.length_drop, List.length_take, Nat.min_eq_left he]

omit [Fintype α] [DecidableEq α] in
/-- Prefixes of safe spines are safe. -/
theorem safe_take {u : Word α} (h : I.SafeFrom I.A.start u) (s : ℕ) :
    I.SafeFrom I.A.start (u.take s) := by
  intro i hi
  have hil : min i s ≤ u.length := by
    have := Finset.mem_range.mp hi
    simp only [List.length_take] at this
    omega
  simpa [List.take_take] using h (min i s) (Finset.mem_range.mpr (by omega))

omit [DecidableEq α] in
/-- The state at a spine cut of a separator word. -/
theorem run_spine {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    {s : ℕ} (hs : s ≤ u.length) :
    runPrefix (reader I) (sepWord u t) s = .pre (I.A.atCut u s) (I.A'.atCut u s) := by
  rw [runPrefix, take_spine u t hs, eval_binary, ite_eq_left (safe_take I hsafe s)]
  rfl

omit [DecidableEq α] in
/-- The state at a target cut of a separator word. -/
theorem run_target {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j e : ℕ} (hj : I.J t = some j) (he : e ≤ t.length) :
    runPrefix (reader I) (sepWord u t) (u.length+1+e) =
      if e ≤ j then .act (I.B.atCut t e) (I.B'.atCut t e)
      else .done (I.B'.atCut t e) (counter I (e-j-1)) := by
  rw [runPrefix, take_target, eval_sep, ite_eq_left ⟨hsafe,hm⟩, eval_target_cut I t hj he]

omit [DecidableEq α] in
/-- A separator word is rejected iff its spine is safe and ends mortal, its target has a
first rejected cut, and fewer than `|SA|` letters follow it. -/
theorem rejected_sep_iff (u t : Word α) :
    (reader I).eval (sepWord u t) ∈ Rej I ↔
      I.SafeFrom I.A.start u ∧ I.Mortal (I.A.run u) ∧
        ∃ j, I.J t = some j ∧ t.length-j < Fintype.card SA := by
  rw [eval_sep]
  by_cases hs : I.SafeFrom I.A.start u ∧ I.Mortal (I.A.run u)
  · rw [ite_eq_left hs]
    cases hj : I.J t with
    | none =>
      have hn := (I.J_eq_none_iff t).mp hj
      rw [eval_active I t (fun i hi => hn i hi.le)]
      change I.B.run t ∈ I.Rej ↔ _
      have hn' : I.B.run t ∉ I.Rej := by simpa [LDFA.atCut] using hn t.length le_rfl
      simp [hn']
    | some j =>
      have hJ := (I.J_eq_some_iff t j).mp hj
      have hf := eval_target_cut I t hj (e := t.length) le_rfl
      simp only [List.take_length] at hf
      rw [hf]
      simp only [Option.some.injEq, hs.1, hs.2, true_and]
      have hex : (∃ k, j = k ∧ t.length-k < Fintype.card SA) ↔
          t.length-j < Fintype.card SA := by
        constructor
        · rintro ⟨k,rfl,h⟩; exact h
        · intro h; exact ⟨j,rfl,h⟩
      rw [hex]
      split
      · have heq : t.length = j := by omega
        change I.B.atCut t t.length ∈ I.Rej ↔ _
        constructor
        · intro _; have := card_A_pos I; omega
        · intro _; simpa [heq] using hJ.1
      · change min (t.length-j-1) (Fintype.card SA-1) + 1 < Fintype.card SA ↔ _
        have := card_A_pos I
        omega
  · rw [ite_eq_right hs]
    change False ↔ _
    rw [false_iff]
    rintro ⟨ha,hm,_⟩
    exact hs ⟨ha,hm⟩

omit [DecidableEq α] in
/-- The first rejected cut of the separator word is the first rejected cut of the target. -/
theorem first_rejected_cut {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    IsFirstRejectedPrefix (reader I) (Rej I) (sepWord u t) (u.length + 1 + j) := by
  have hJ := (I.J_eq_some_iff t j).mp hj
  refine ⟨by simp only [length_sepWord]; omega, ?_, ?_⟩
  · change runPrefix (reader I) (sepWord u t) (u.length+1+j) ∈ Rej I
    rw [run_target I hsafe hm hj hJ.2.1, ite_eq_left le_rfl]
    exact hJ.1
  · intro k hk
    change runPrefix (reader I) (sepWord u t) k ∉ Rej I
    by_cases hkp : k ≤ u.length
    · rw [run_spine I hsafe hkp]
      exact not_false
    · have he : k = u.length+1+(k-(u.length+1)) := by omega
      have hlt : k-(u.length+1) < j := by omega
      rw [he, run_target I hsafe hm hj (by omega), ite_eq_left hlt.le]
      exact hJ.2.2 _ hlt

omit [DecidableEq α] in
/-- At a cross comparison, `Pi` tests the head pair at its cuts. -/
theorem pi_at_cross {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j s e : ℕ} (hj : I.J t = some j)
    (hs : s ≤ u.length) (he : e ≤ t.length) :
    Pi I (runPrefix (reader I) (sepWord u t) s)
      (runPrefix (reader I) (sepWord u t) (u.length+1+e)) ↔
        (I.A'.atCut u s, I.B'.atCut t e) ∈ I.Head := by
  rw [run_spine I hsafe hs, run_target I hsafe hm hj he]
  split <;> rfl

/-- On a separator word, `HasPi` is a head event of the pair. -/
theorem hasPi_sep_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    HasPi I (sepWord u t) ↔ I.HasHeadEvent u t := by
  constructor
  · rintro ⟨p, _, hp, s, e, ha, hpi⟩
    have hpos := (separator_unique u t p).mp hp
    subst p
    obtain ⟨e',he',heq,hal⟩ := anchored_target u t ha
    subst e
    exact ⟨s, Finset.mem_range.mpr (by have := ha.1; omega),
      e', Finset.mem_range.mpr (by omega), ⟨ha.1, he', hal⟩,
      (pi_at_cross I hsafe hm hj ha.1 he').mp hpi⟩
  · rintro ⟨s,hs,e,he,⟨hs',he',hal⟩,hhead⟩
    exact ⟨u.length, count_sepWord u t, (separator_unique u t _).mpr rfl,
      s, u.length+1+e, (anchored_iff u t hs' he').mpr hal,
      (pi_at_cross I hsafe hm hj hs' he').mpr hhead⟩

omit [DecidableEq α] in
/-- On a separator word, the absence of admitted comparisons is the absence of events. -/
theorem no_admitted_iff {u t : Word α} (hsafe : I.SafeFrom I.A.start u)
    (hm : I.Mortal (I.A.run u)) {j : ℕ} (hj : I.J t = some j) :
    (∀ s e, IsComp (sepWord u t) s e →
      ¬ Adm I (runPrefix (reader I) (sepWord u t) s) (runPrefix (reader I) (sepWord u t) e)) ↔
    (∀ s ∈ Finset.range (u.length+1), ∀ e ∈ Finset.range (t.length+1), ¬ I.Event u t s e) := by
  constructor
  · intro h s hs e he hev
    obtain ⟨⟨hs',he',hp⟩, ⟨k,hk,hk'⟩,hg⟩ := hev
    have hkj : j = k := by simpa [hj] using hk
    subst k
    apply h s (u.length+1+e) ((cross_comparison_iff u t hs' he').mpr hp)
    rw [run_spine I hsafe hs', run_target I hsafe hm hj he', ite_eq_left hk']
    exact hg
  · intro h s e hc hadm
    have hel : e ≤ (sepWord u t).length := hc.2.1
    by_cases hs : s ≤ u.length
    · by_cases he : e ≤ u.length
      · exact no_pre_comparison u t hc.1 he hc
      · have heq : e = u.length+1+(e-(u.length+1)) := by omega
        have he' : e-(u.length+1) ≤ t.length := by simp only [length_sepWord] at hel; omega
        have hp := (cross_comparison_iff u t hs he').mp (heq ▸ hc)
        rw [heq, run_spine I hsafe hs, run_target I hsafe hm hj he'] at hadm
        split at hadm
        next hle =>
          exact h s (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega))
            ⟨⟨hs,he',hp⟩, ⟨j, by simp [hj], hle⟩, hadm⟩
        next => exact hadm
    · have heq : s = u.length+1+(s-(u.length+1)) := by omega
      have hs' : s-(u.length+1) ≤ t.length := by
        simp only [length_sepWord] at hel
        have := hc.1; omega
      rw [heq, run_target I hsafe hm hj hs'] at hadm
      split at hadm <;> exact hadm

/-- A separator word is a Π-hole iff the pair is a mortal hole. -/
theorem piHole_sep_iff (u t : Word α) : PiHole I (sepWord u t) ↔ I.IsMortalHole u t := by
  constructor
  · rintro ⟨hh,hpi⟩
    have hc := (isReaderHole_iff _ _ _ _).mp hh
    obtain ⟨hs,hm,j,hj,hlen⟩ := (rejected_sep_iff I u t).mp hc.1
    refine ⟨⟨hs, by simp [hj], ?_, (hasPi_sep_iff I hs hm hj).mp hpi⟩,
      hm, j, by simp [hj], hlen⟩
    apply (no_admitted_iff I hs hm hj).mp
    intro s e hcomp
    exact hc.2 s e hcomp.1 hcomp.2.1 hcomp.2.2
  · rintro ⟨⟨hs,_,hne,hhead⟩,hm,j,hj,hlen⟩
    have hj' : I.J t = some j := by simpa using hj
    refine ⟨(isReaderHole_iff _ _ _ _).mpr ⟨(rejected_sep_iff I u t).mpr
      ⟨hs,hm,j,hj',hlen⟩, ?_⟩, (hasPi_sep_iff I hs hm hj').mpr hhead⟩
    intro s e hse he hp
    exact (no_admitted_iff I hs hm hj').mpr hne s e ⟨hse,he,hp⟩

/-- The Π-holes are exactly the separator words of mortal holes. -/
theorem piReader_iff (w : List (Option α)) :
    PiHole I w ↔ ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  constructor
  · intro h
    obtain ⟨p,hcount,_⟩ := h.2
    obtain ⟨u,t,rfl⟩ := exists_sepWord w hcount
    exact ⟨u,t,rfl,(piHole_sep_iff I u t).mp h⟩
  · rintro ⟨u,t,rfl,h⟩
    exact (piHole_sep_iff I u t).mpr h

/-- The same in terms of the lettered monitor of the reader. -/
theorem ofReader_pi_iff (w : List (Option α)) :
    ((DeciNSSE.LetteredHierarchy.ofReader (reader I) (Adm I) (Rej I)).IsHole w ∧ HasPi I w) ↔
      ∃ u t, w = sepWord u t ∧ I.IsMortalHole u t := by
  rw [← piReader_iff]
  by_cases hw : w = []
  · subst w
    have hn : ¬ HasPi I [] := by rintro ⟨p,h,_⟩; simp at h
    simp [PiHole, hn]
  · rw [DeciNSSE.LetteredHierarchy.isHole_ofReader_iff _ _ _ hw]
    rfl

private def Post : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB') → Prop
  | .pre _ _ => False
  | _ => True

omit [DecidableEq α] in
private theorem post_step (q : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB'))
    (hq : Post q) (c : Option α) : Post ((reader I).step q c) := by
  cases q with
  | pre a a' => exact hq.elim
  | act b b' =>
    cases c with
    | none => trivial
    | some c =>
      change Post (if b ∈ I.Rej then _ else _)
      split <;> trivial
  | done b' k => cases c <;> trivial
  | sink => cases c <;> trivial

omit [DecidableEq α] in
private theorem post_separator (q : State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB'))
    (hq : Post q) (v : List (Option α)) (hv : none ∈ v) :
    (reader I).evalFrom q v = .sink := by
  induction v generalizing q with
  | nil => simp at hv
  | cons c v ih =>
    cases c with
    | none =>
      cases q <;> first | exact hq.elim | exact eval_sink I v
    | some c =>
      rw [DFA.evalFrom_cons]
      exact ih _ (post_step I q hq (some c)) (by simpa using hv)

/-- A rejected word is a separator word. -/
theorem rejected_word_form (w : List (Option α)) (hr : (reader I).eval w ∈ Rej I) :
    ∃ u t, w = sepWord u t := by
  have split_word (v : List (Option α)) :
      (∃ u : Word α, v = u.map some) ∨
        (∃ u : Word α, ∃ z, v = sepWord u [] ++ z) := by
    induction v with
    | nil => exact Or.inl ⟨[],rfl⟩
    | cons c v ih =>
      cases c with
      | none => exact Or.inr ⟨[],v,rfl⟩
      | some c =>
        rcases ih with ⟨u,rfl⟩ | ⟨u,z,rfl⟩
        · exact Or.inl ⟨c :: u,rfl⟩
        · exact Or.inr ⟨c :: u,z,rfl⟩
  rcases split_word w with ⟨u,rfl⟩ | ⟨u,z,rfl⟩
  · rw [eval_binary] at hr
    split at hr <;> exact hr.elim
  · have he : (reader I).eval (sepWord u [] ++ z) =
        (reader I).evalFrom ((reader I).eval (sepWord u [])) z :=
      DFA.evalFrom_of_append _ _ _ _
    rw [he, eval_separator] at hr
    split at hr
    next hgood =>
      have hn : none ∉ z := by
        intro hz
        rw [post_separator I _ (by trivial) z hz] at hr
        exact hr
      obtain ⟨t,ht⟩ := plain_of_no_separator z (List.count_eq_zero.mpr hn)
      exact ⟨u,t,by simp [ht, sepWord]⟩
    next => rw [eval_sink] at hr; exact hr.elim

/-- A rejected word has exactly one separator. -/
theorem rejected_count_separator (w : List (Option α)) (hr : (reader I).eval w ∈ Rej I) :
    w.count none = 1 := by
  obtain ⟨u,t,rfl⟩ := rejected_word_form I w hr
  exact count_sepWord u t

end DeciENSSE.Core.Words.Mortal
