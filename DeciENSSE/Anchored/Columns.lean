import DeciENSSE.Anchored.Agree
import DeciNSSE.Holes.Columns

/-! # The positive column automaton

The column automaton of a monitor summarizes a tuple of blocks, read as a right-aligned
padded word of columns, by the data that determine the derived monitor on the tuple. The
positive column automaton runs it for `D` and for the monitor carrying `F`, `R` and `S`,
and adds, for each track, the weighted terminal events inside the block, the pending `S'`
test at its end, and the letter test of its first letter. These summaries determine the
derived channel on the tuple, so short sub-words with the same summary give an agreement of
the derived monitors and channels.

## Main declarations

- `weighted`, `term_decode`: weighted terminal events, and terminal events decoded.
- `PCS`, `psumm`, `pcolDFA`, `pcolEval`: states, intended summaries, the automaton, and its
  correctness on valid column words.
- `pcolBound`, `card_PCS`: the number of states.
- `pos_type_of_psumm`: equal summaries give the same derived channel rows.
- `exists_short_pos_tuple`, `exists_short_pos_letters`: short tuples with the same
  summary, and short blocks with an agreement of the derived monitors and channels.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth
open DeciNSSE.Packets
variable {Γ C : Type*} (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)

/-- Weighted terminal events strictly inside a block: a position before its end is in
`S'` with the final label and carries a letter in `Φ`. -/
def weighted (c : Option C) (X : List Γ) (d : C) : Prop :=
  ∃ p < X.length, P.S' (zlab D ℓ c X p) (some (d, ℓ)) ∧ At P.Φ X p

/-- Appending a letter does not change the letter tests before it. -/
theorem at_snoc_lt (Φ : Γ → Prop) (X : List Γ) (z : Γ) {p : ℕ}
    (hp : p < X.length) : At Φ (X ++ [z]) p ↔ At Φ X p := by
  simp only [At, List.getElem?_append_left hp]

/-- The letter test at the appended position tests the appended letter. -/
theorem at_snoc_last (Φ : Γ → Prop) (X : List Γ) (z : Γ) :
    At Φ (X ++ [z]) X.length ↔ Φ z := by simp [At]

/-- Appending a letter in `Φ` adds the pending `S'` test at the end of the block to the
weighted events. -/
theorem weighted_snoc (c : Option C) (X : List Γ) (z : Γ) (d : C) :
    weighted D P ℓ c (X ++ [z]) d ↔ weighted D P ℓ c X d ∨
      (P.S' (zlab D ℓ c X X.length) (some (d, ℓ)) ∧ P.Φ z) := by
  constructor
  · rintro ⟨p, hp, hr, hf⟩
    have hp' : p ≤ X.length := by simp at hp; omega
    rw [zlab_snoc_le D ℓ c X z hp'] at hr
    rcases lt_or_eq_of_le hp' with hp' | rfl
    · exact Or.inl ⟨p, hp', hr, (at_snoc_lt _ _ _ hp').mp hf⟩
    · exact Or.inr ⟨hr, (at_snoc_last _ _ _).mp hf⟩
  · rintro (⟨p, hp, hr, hf⟩ | ⟨hr, hf⟩)
    · exact ⟨p, by simp; omega, by rwa [zlab_snoc_le D ℓ c X z hp.le],
        (at_snoc_lt _ _ _ hp).mpr hf⟩
    · exact ⟨X.length, by simp, by rwa [zlab_snoc_le D ℓ c X z le_rfl],
        (at_snoc_last _ _ _).mpr hf⟩

/-- Terminal events are `S` events, weighted events, or the `S'` test at the marker. -/
theorem term_decode (c : Option C) (X : List Γ) (d : C) :
    term D P ℓ c X d ↔
      (∃ p ≤ X.length, P.S (zlab D ℓ c X p) (some (d, ℓ))) ∨
      weighted D P ℓ c X d ∨
      (P.S' (zlab D ℓ c X X.length) (some (d, ℓ)) ∧ P.Φ ℓ) := by
  constructor
  · rintro ⟨p, hp, hr | ⟨hr, hf⟩⟩
    · exact Or.inl ⟨p, hp, hr⟩
    · rcases lt_or_eq_of_le hp with hp | rfl
      · exact Or.inr (Or.inl ⟨p, hp, hr, (at_snoc_lt _ _ _ hp).mp hf⟩)
      · exact Or.inr (Or.inr ⟨hr, (at_snoc_last _ _ _).mp hf⟩)
  · rintro (⟨p, hp, hr⟩ | ⟨p, hp, hr, hf⟩ | ⟨hr, hf⟩)
    · exact ⟨p, hp, Or.inl hr⟩
    · exact ⟨p, hp.le, Or.inr ⟨hr, (at_snoc_lt _ _ _ hp).mpr hf⟩⟩
    · exact ⟨X.length, le_rfl, Or.inr ⟨hr, (at_snoc_last _ _ _).mpr hf⟩⟩

/-- States of the positive column automaton: the column states of `D` and of
`withPos D P`, the weighted events, the pending `S'` tests at the end of each track, and the
letter test of the first letter of each track (`none` for an empty track). -/
abbrev PCS (C : Type*) (k : ℕ) :=
  CS C k × CS C k × (Fin k → Option C → C → Prop) ×
    (Fin k → Option C → C → Prop) × (Fin k → Option Prop)

variable (k : ℕ)

/-- The intended positive summary of a tuple of blocks. -/
def psumm (Ws : Fin k → List Γ) : PCS C k :=
  (summ D ℓ k Ws, summ (withPos D P) ℓ k Ws,
   fun a c d => weighted D P ℓ c (Ws a) d,
   fun a c d => P.S' (zlab D ℓ c (Ws a) (Ws a).length) (some (d, ℓ)),
   fun a => (Ws a).head?.map P.Φ)

/-- The transition of the positive column automaton; padding leaves the positive fields
unchanged. -/
def pcolStep (s : PCS C k) (col : Fin k → Option Γ) : PCS C k :=
  ((colDFA D ℓ k).step s.1 col, (colDFA (withPos D P) ℓ k).step s.2.1 col,
   fun a c d => match col a with
     | none => s.2.2.1 a c d
     | some z => s.2.2.1 a c d ∨ (s.2.2.2.1 a c d ∧ P.Φ z),
   fun a c d => match col a with
     | none => s.2.2.2.1 a c d
     | some z => P.S' (some (s.1.1 a c, z)) (some (d, ℓ)),
   fun a => match s.2.2.2.2 a with
     | some b => some b
     | none => (col a).map P.Φ)

/-- The positive column automaton. -/
def pcolDFA : DFA (Fin k → Option Γ) (PCS C k) where
  start := psumm D P ℓ k (fun _ => [])
  step := pcolStep D P ℓ k
  accept := ∅

/-- The first-letter test after appending a letter. -/
theorem first_snoc (X : List Γ) (z : Γ) :
    (X ++ [z]).head?.map P.Φ =
      match X.head?.map P.Φ with
      | some b => some b
      | none => some (P.Φ z) := by cases X <;> rfl

/-- On a valid column word, the positive column automaton computes the positive summary of
the decoded tuple. -/
theorem pcolEval (w : List (Fin k → Option Γ)) (hw : Valid w) :
    (pcolDFA D P ℓ k).eval w = psumm D P ℓ k (dec w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w col ih =>
    have hv := hw.sublist (List.sublist_append_left _ _)
    have hn := colEval D ℓ k (w ++ [col]) hw
    have hp := colEval (withPos D P) ℓ k (w ++ [col]) hw
    rw [DFA.eval_append_singleton, colEval D ℓ k w hv] at hn
    rw [DFA.eval_append_singleton, colEval (withPos D P) ℓ k w hv] at hp
    rw [DFA.eval_append_singleton, ih hv]
    change pcolStep D P ℓ k (psumm D P ℓ k (dec w)) col = _
    refine Prod.ext hn (Prod.ext hp (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · funext a c d
      simp only [pcolStep, psumm, dec_snoc]
      cases col a with
      | none => simp
      | some z => simpa using propext (weighted_snoc D P ℓ c (dec w a) z d).symm
    · funext a c d
      simp only [pcolStep, psumm, dec_snoc]
      cases col a with
      | none => simp
      | some z => simp [summ, zlab_snoc_last]
    · funext a
      simp only [pcolStep, psumm, dec_snoc]
      cases col a with
      | none => simp; cases (dec w a).head?.map P.Φ <;> rfl
      | some z => simpa using (first_snoc P (dec w a) z).symm

/-- The positive column automaton has finitely many states. -/
instance instFintypePCS [Fintype C] [DecidableEq C] : Fintype (PCS C k) :=
  @instFintypeProd _ _ inferInstance
    (@instFintypeProd _ _ inferInstance
      (@instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance)))

/-- The number of states of the positive column automaton for `N` cores and `k` tracks; it
counts both column states in full. -/
def pcolBound (N k : ℕ) : ℕ :=
  colBound N k * colBound N k * (((2 ^ N) ^ (N + 1)) ^ k) *
    (((2 ^ N) ^ (N + 1)) ^ k) * 3 ^ k

/-- The positive column automaton has `pcolBound |C| k` states. -/
theorem card_PCS [Fintype C] [DecidableEq C] :
    Fintype.card (PCS C k) = pcolBound (Fintype.card C) k := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  simp [Fintype.card_option, pcolBound, colBound, mul_assoc]

/-- Every tuple of blocks has a tuple of sub-words, each shorter than `pcolBound |C| k`,
with the same positive summary. -/
theorem exists_short_pos_tuple [Fintype C] [DecidableEq C] (Ws : Fin k → List Γ) :
    ∃ Ws' : Fin k → List Γ, (∀ a, (Ws' a).Sublist (Ws a)) ∧
      (∀ a, (Ws' a).length < pcolBound (Fintype.card C) k) ∧
      psumm D P ℓ k Ws' = psumm D P ℓ k Ws := by
  obtain ⟨Ws', h1, h2, h3⟩ := exists_short_conv (fun x => (pcolDFA D P ℓ k).eval x)
    (fun x y a h => by simp only [DFA.eval_append_singleton]; rw [h]) Ws
  refine ⟨Ws', h1, fun a => (h2 a).trans_eq (card_PCS k), ?_⟩
  have e1 := pcolEval D P ℓ k _ (valid_conv Ws')
  have e2 := pcolEval D P ℓ k _ (valid_conv Ws)
  rw [dec_conv] at e1 e2
  rw [← e1, ← e2]
  exact h3

/-- The derived letter test in terms of the first-letter test. -/
theorem phi_decode (X : List Γ) :
    At P.Φ (X ++ [ℓ]) 0 ↔ (X.head?.map P.Φ).getD (P.Φ ℓ) := by
  cases X <;> simp [At]

/-- Equal positive summaries give the same rows of the derived channel; the `S'` row is
the `R` row. -/
theorem pos_type_of_psumm {Ws Ws' : Fin k → List Γ}
    (hs : psumm D P ℓ k Ws' = psumm D P ℓ k Ws) (a b : Fin k) :
    (∀ c, (posDer D P ℓ).F c (Ws' a) ↔ (posDer D P ℓ).F c (Ws a)) ∧
    (∀ c c', (posDer D P ℓ).R (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (posDer D P ℓ).R (some (c, Ws a)) (some (c', Ws b))) ∧
    (∀ c c', (posDer D P ℓ).S (some (c, Ws' a)) (some (c', Ws' b)) ↔
      (posDer D P ℓ).S (some (c, Ws a)) (some (c', Ws b))) ∧
    ((posDer D P ℓ).Φ (Ws' a) ↔ (posDer D P ℓ).Φ (Ws a)) := by
  have hn := congrArg Prod.fst hs
  have hp := congrArg (fun s : PCS C k => s.2.1) hs
  have hc : ∀ a c, fcore D ℓ c (Ws' a) = fcore D ℓ c (Ws a) := fun a c =>
    congrFun (congrFun (congrArg Prod.fst hn) a) c
  have ht : ∀ a c d, term D P ℓ c (Ws' a) d ↔ term D P ℓ c (Ws a) d := by
    intro a c d
    rw [term_decode, term_decode]
    have hS := congrFun (congrFun (congrFun (congrArg (fun s => s.2.1) hp) a) c) d
    have hW := congrFun (congrFun (congrFun (congrArg (fun s : PCS C k => s.2.2.1) hs) a) c) d
    have hpend := congrFun (congrFun (congrFun
      (congrArg (fun s : PCS C k => s.2.2.2.1) hs) a) c) d
    exact or_congr (Iff.of_eq hS)
      (or_congr (Iff.of_eq hW) (and_congr (Iff.of_eq hpend) Iff.rfl))
  refine ⟨?_, (der_type_of_summ (withPos D P) ℓ k hp a b).2.2.2.1, ?_, ?_⟩
  · intro c
    change P.F (fcore D ℓ c (Ws' a)) ℓ ∨ term D P ℓ c (Ws' a) (fcore D ℓ c (Ws' a)) ↔ _
    rw [hc, ht]
    rfl
  · intro c c'
    change term D P ℓ c (Ws' a) (fcore D ℓ c' (Ws' b)) ↔ _
    rw [hc, ht]
    rfl
  · change At P.Φ (Ws' a ++ [ℓ]) 0 ↔ At P.Φ (Ws a ++ [ℓ]) 0
    rw [phi_decode, phi_decode]
    exact Iff.of_eq (congrArg (fun x : Option Prop => x.getD (P.Φ ℓ))
      (congrFun (congrArg (fun s : PCS C k => s.2.2.2.2) hs) a))

/-- Every list of at most `k` blocks has a map sending each block to a sub-word shorter than
`pcolBound |C| k`, with an agreement of the derived monitors and channels on the list. -/
theorem exists_short_pos_letters [Fintype C] [DecidableEq C] (E : List (List Γ))
    (hk : E.length ≤ k) :
    ∃ ψ : List Γ → List Γ,
      PosAgree (der D ℓ) (der D ℓ) (posDer D P ℓ) (posDer D P ℓ) ψ E ∧
      ∀ X ∈ E, (ψ X).Sublist X ∧ (ψ X).length < pcolBound (Fintype.card C) k := by
  classical
  set Ws : Fin k → List Γ := fun a => E.getD a.1 [] with hWs
  obtain ⟨Ws', hsub, hlen, hsumm⟩ := exists_short_pos_tuple D P ℓ k Ws
  have hT := der_type_of_summ D ℓ k (congrArg Prod.fst hsumm)
  have hP := pos_type_of_psumm D P ℓ k hsumm
  have hidx : ∀ X ∈ E, E.idxOf X < k := fun X hX =>
    (List.idxOf_lt_length_of_mem hX).trans_le hk
  let idx : ∀ X ∈ E, Fin k := fun X hX => ⟨E.idxOf X, hidx X hX⟩
  have hWsidx : ∀ X (hX : X ∈ E), Ws (idx X hX) = X := fun X hX => by
    simp only [hWs, idx]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hX), List.getElem_idxOf]
  let ψ : List Γ → List Γ := fun X => if hX : X ∈ E then Ws' (idx X hX) else X
  have hψ : ∀ X (hX : X ∈ E), ψ X = Ws' (idx X hX) := fun X hX => dite_eq_left hX
  have hn : Agree (der D ℓ) (der D ℓ) ψ E := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      rw [hψ X hX, hψ Y hY, (hT (idx X hX) (idx Y hY)).1,
        hWsidx X hX, hWsidx Y hY] at hXY
      exact hXY
    · intro X hX c
      rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.1, hWsidx X hX]
    · intro X hX c
      rw [hψ X hX, (hT (idx X hX) (idx X hX)).2.2.1, hWsidx X hX]
    · intro L L' hL hL'
      rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
      · simp [derΛ]
      · simp [derΛ]
      · simp [derΛ]
      · simp only [mapLab_some]
        rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.1,
          hWsidx X hL, hWsidx Y hL']
    · intro L L' hL hL'
      rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
      · simp [derΛf]
      · simp [derΛf]
      · simp [derΛf]
      · simp only [mapLab_some]
        rw [hψ X hL, hψ Y hL', (hT (idx X hL) (idx Y hL')).2.2.2.2,
          hWsidx X hL, hWsidx Y hL']
  have hr : ∀ L L', LabIn E L → LabIn E L' →
      ((posDer D P ℓ).R (mapLab ψ id L) (mapLab ψ id L') ↔ (posDer D P ℓ).R L L') := by
    intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · simp only [mapLab_some]
      rw [hψ X hL, hψ Y hL', (hP (idx X hL) (idx Y hL')).2.1,
        hWsidx X hL, hWsidx Y hL']
  refine ⟨ψ, ⟨hn, ⟨hn.start, hn.inj, hn.κ, ?_, hr, ?_⟩, hr, ?_⟩, ?_⟩
  · intro X hX c
    change (posDer D P ℓ).F c (ψ X) ↔ _
    rw [hψ X hX, (hP (idx X hX) (idx X hX)).1, hWsidx X hX]
    rfl
  · intro L L' hL hL'
    rcases L with _ | ⟨c, X⟩ <;> rcases L' with _ | ⟨c', Y⟩
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · change (posDer D P ℓ).S (some (c, ψ X)) (some (c', ψ Y)) ↔ _
      rw [hψ X hL, hψ Y hL', (hP (idx X hL) (idx Y hL')).2.2.1,
        hWsidx X hL, hWsidx Y hL']
      rfl
  · intro X hX
    rw [hψ X hX, (hP (idx X hX) (idx X hX)).2.2.2, hWsidx X hX]
  · intro X hX
    rw [hψ X hX]
    refine ⟨?_, hlen _⟩
    have := hsub (idx X hX)
    rwa [hWsidx X hX] at this

end DeciENSSE.Anchored
