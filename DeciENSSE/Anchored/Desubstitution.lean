import DeciENSSE.Anchored.Channel
import DeciNSSE.Holes.Hierarchy.Canonical

/-! # Desubstitution of positive channels

The derived channel of a channel `P` along a marker `ℓ` reads words of blocks. It is
chosen so that a nonempty block word avoiding the marker satisfies the derived positive
condition exactly when its expansion satisfies the positive condition of `P`: a
comparison of the expansion becomes a comparison of blocks or a test against the final
label, and its continuation letter becomes the first letter of an expanded block. Along a
marker sequence the derived channels form a tower beside the tower of derived monitors,
and positive holes correspond at every level and along the canonical hierarchy.

## Main declarations

- `term`, `posDer`: terminal events of a block, and the derived channel.
- `continuation_cutP`: continuation letters of an expansion lie at block boundaries.
- `pos_der_iff`, `posHole_der_iff`: desubstitution of the positive condition and of
  positive holes.
- `posTower`, `pos_expandTo_iff`, `pos_tower_iff`, `pos_hierOf_iff`: the tower of derived
  channels, and positive holes along it and along the canonical hierarchy.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

variable {Γ C : Type*}

/-- Terminal events of a block: some position of `X ℓ`, the marker included, is in `S`
with the final label `(E, ℓ)`, or in `S'` with it while its letter is in `Φ`. -/
def term (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (c : Option C) (X : List Γ) (E : C) : Prop :=
  ∃ p ≤ X.length, P.S (zlab D ℓ c X p) (some (E, ℓ)) ∨
    (P.S' (zlab D ℓ c X p) (some (E, ℓ)) ∧ At P.Φ (X ++ [ℓ]) p)

/-- The derived channel along the marker `ℓ`. The final test also accepts terminal events
of the last block; `S` relates a block to the final label through its terminal events;
`R` and `S'` are the derived ladder of `R`; `Φ` tests the first letter of a block followed
by the marker. -/
def posDer (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ) :
    PosChan (List Γ) (Option C) where
  F c X := P.F (fcore D ℓ c X) ℓ ∨ term D P ℓ c X (fcore D ℓ c X)
  R := derΛ (withPos D P) ℓ
  S | some (c, X), some (c', X') => term D P ℓ c X (fcore D ℓ c' X')
    | _, _ => False
  S' := derΛ (withPos D P) ℓ
  Φ X := At P.Φ (X ++ [ℓ]) 0

/-- Reading a letter inside an expanded block, including its final marker. -/
theorem getElem?_expand (ℓ : Γ) (v : List (List Γ)) (i : ℕ) (hi : i < v.length)
    (r : ℕ) (hr : r ≤ v[i].length) :
    (expand ℓ v)[cutP ℓ v i + r]? = (v[i] ++ [ℓ])[r]? := by
  rw [expand_split ℓ v i hi]
  rw [List.getElem?_append_right (by simp [cutP])]
  simp only [cutP, Nat.add_sub_cancel_left]
  rw [show v[i] ++ ℓ :: expand ℓ (v.drop (i + 1)) =
    (v[i] ++ [ℓ]) ++ expand ℓ (v.drop (i + 1)) by simp]
  exact List.getElem?_append_left (by simp; omega)

/-- Cuts add the lengths of the intervening expanded blocks. -/
theorem cutP_add (ℓ : Γ) (v : List (List Γ)) (i j : ℕ) :
    cutP ℓ v (i + j) = cutP ℓ v i + (expand ℓ ((v.drop i).take j)).length := by
  simp only [cutP, List.take_add, expand_append, List.length_append]

/-- The length of an expansion splits at every block cut. -/
theorem cutP_tail (ℓ : Γ) (v : List (List Γ)) (i : ℕ) :
    (expand ℓ v).length = cutP ℓ v i + (expand ℓ (v.drop i)).length := by
  rw [cutP, ← List.length_append, ← expand_append, List.take_append_drop]

/-- For a comparison of an expansion between blocks `a < b` with a common block suffix,
the continuation position is the cut before block `a + 1 + |v| - (b + 1)`, the
continuation position of the comparison of blocks. -/
theorem continuation_cutP (ℓ : Γ) (v : List (List Γ))
    (a b : ℕ) (ha : a < v.length) (hb : b < v.length)
    (xs xe Y : List Γ) (hx : v[a] = xs ++ Y) (hy : v[b] = xe ++ Y)
    (hc : v.drop (b + 1) <+: v.drop (a + 1)) :
    (cutP ℓ v a + xs.length) + (expand ℓ v).length - (cutP ℓ v b + xe.length) =
      cutP ℓ v (a + 1 + v.length - (b + 1)) := by
  have ht := List.prefix_iff_eq_take.mp hc
  have hl : (v.drop (b + 1)).length = v.length - (b + 1) := List.length_drop
  rw [hl] at ht
  have he := cutP_add ℓ v (a + 1) (v.length - (b + 1))
  rw [← ht] at he
  have htail := cutP_tail ℓ v (b + 1)
  have hca := cutP_succ ℓ v a ha
  have hcb := cutP_succ ℓ v b hb
  rw [hx, List.length_append] at hca
  rw [hy, List.length_append] at hcb
  have hi : a + 1 + v.length - (b + 1) = a + 1 + (v.length - (b + 1)) := by omega
  rw [hi]
  omega

/-- The derivative letter test is exactly the lower test at a block boundary. -/
theorem at_posDer_iff (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (v : List (List Γ)) (i : ℕ) (hi : i < v.length) :
    At (posDer D P ℓ).Φ v i ↔ At P.Φ (expand ℓ v) (cutP ℓ v i) := by
  simp only [At, List.getElem?_eq_getElem hi, Option.some.injEq, exists_eq_left']
  change (∃ a, (v[i] ++ [ℓ])[0]? = some a ∧ P.Φ a) ↔ _
  rw [← getElem?_expand ℓ v i hi 0 (Nat.zero_le _), Nat.add_zero]

/-- The positive condition of an expansion in block coordinates. A terminal event may lie
in any block; the last block is folded into the derived final test. -/
theorem pos_expand_iff (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (v : List (List Γ)) (j : ℕ) (hlen : v.length = j + 1)
    (hℓ : ∀ X ∈ v, ℓ ∉ X) :
    Pos D P (expand ℓ v) ↔
    P.F (fcore D ℓ ((der D ℓ).core v j) v[j]) ℓ ∨
    (∃ a b, ∃ (ha : a < v.length) (hb : b < v.length), a < b ∧
      v.drop (b + 1) <+: v.drop (a + 1) ∧
      derΛ (withPos D P) ℓ (some ((der D ℓ).core v a, v[a]))
        (some ((der D ℓ).core v b, v[b])) ∧
      At (posDer D P ℓ).Φ v (a + 1 + v.length - (b + 1))) ∨
    (∃ a, ∃ ha : a < v.length,
      term D P ℓ ((der D ℓ).core v a) v[a]
        (fcore D ℓ ((der D ℓ).core v j) v[j])) := by
  have hj : j < v.length := by omega
  have hfin := label_expand_length D ℓ v j hlen
  unfold Pos
  rw [hfin, exists_some_eq_iff]
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨s, e, ⟨hse, _, hc⟩, he, hr, hφ⟩
      obtain ⟨a, b, ha, hb, hab, xs, xe, Y, hx, hy, rfl, rfl, hcomp⟩ :=
        (alignment ℓ v hℓ hse he).mp hc
      have hpa : xs.length ≤ v[a].length := by rw [hx]; simp
      have hpb : xe.length ≤ v[b].length := by rw [hy]; simp
      rw [label_expand D ℓ v a ha hpa, label_expand D ℓ v b hb hpb] at hr
      refine ⟨a, b, ha, hb, hab, hcomp, ⟨xs, xe, Y, hx, hy, hr⟩, ?_⟩
      rw [at_posDer_iff D P ℓ v _ (by omega)]
      rwa [continuation_cutP ℓ v a b ha hb xs xe Y hx hy hcomp] at hφ
    · rintro ⟨a, b, ha, hb, hab, hc, ⟨xs, xe, Y, hx, hy, hr⟩, hφ⟩
      have hpa : xs.length ≤ v[a].length := by rw [hx]; simp
      have hpb : xe.length ≤ v[b].length := by rw [hy]; simp
      have he := pos_lt ℓ v hb hpb
      have hse : cutP ℓ v a + xs.length < cutP ℓ v b + xe.length := by
        have := cutP_succ ℓ v a ha
        have := cutP_mono ℓ v (show a + 1 ≤ b by omega)
        omega
      refine ⟨_, _, ⟨hse, he.le, (alignment ℓ v hℓ hse he).mpr
        ⟨a, b, ha, hb, hab, xs, xe, Y, hx, hy, rfl, rfl, hc⟩⟩, he, ?_, ?_⟩
      · rw [label_expand D ℓ v a ha hpa, label_expand D ℓ v b hb hpb]
        exact hr
      · rw [continuation_cutP ℓ v a b ha hb xs xe Y hx hy hc]
        exact (at_posDer_iff D P ℓ v _ (by omega)).mp hφ
  · constructor
    · rintro (⟨s, hs, hr⟩ | ⟨s, hs, hr, hφ⟩)
      · obtain ⟨a, ha, p, hp, rfl⟩ := pos_decomp ℓ v hs
        rw [label_expand D ℓ v a ha hp] at hr
        exact ⟨a, ha, p, hp, Or.inl hr⟩
      · obtain ⟨a, ha, p, hp, rfl⟩ := pos_decomp ℓ v hs
        rw [label_expand D ℓ v a ha hp] at hr
        unfold At at hφ
        rw [getElem?_expand ℓ v a ha p hp] at hφ
        exact ⟨a, ha, p, hp, Or.inr ⟨hr, hφ⟩⟩
    · rintro ⟨a, ha, p, hp, hr | ⟨hr, hφ⟩⟩
      · exact Or.inl ⟨_, pos_lt ℓ v ha hp, by
          rw [label_expand D ℓ v a ha hp]; exact hr⟩
      · refine Or.inr ⟨_, pos_lt ℓ v ha hp, ?_, ?_⟩
        · rw [label_expand D ℓ v a ha hp]; exact hr
        · unfold At
          rw [getElem?_expand ℓ v a ha p hp]
          exact hφ

/-- Positive desubstitution: a nonempty block word avoiding the marker satisfies the
derived positive condition iff its expansion satisfies the positive condition. -/
theorem pos_der_iff (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (v : List (List Γ)) (hv : v ≠ []) (hℓ : ∀ X ∈ v, ℓ ∉ X) :
    Pos (der D ℓ) (posDer D P ℓ) v ↔ Pos D P (expand ℓ v) := by
  obtain ⟨j, hlen⟩ : ∃ j, v.length = j + 1 :=
    ⟨v.length - 1, by have := List.length_pos_iff.mpr hv; omega⟩
  have hj : j < v.length := by omega
  have hfin : (der D ℓ).label v v.length = some ((der D ℓ).core v j, v[j]) := by
    rw [hlen]; exact Lettered.label_succ _ _ hj
  rw [pos_expand_iff D P ℓ v j hlen hℓ]
  unfold Pos
  rw [hfin, exists_some_eq_iff]
  constructor
  · rintro (hF | hR | hS | hS')
    · rcases hF with hF | ht
      · exact Or.inl hF
      · exact Or.inr (Or.inr ⟨j, hj, ht⟩)
    · obtain ⟨s, e, hc, he, hr, hφ⟩ := hR
      cases s with
      | zero => exact False.elim hr
      | succ a =>
        obtain ⟨b, rfl⟩ : ∃ b, e = b + 1 := ⟨e - 1, by have := hc.1; omega⟩
        have ha : a < v.length := by have := hc.1; omega
        have hb : b < v.length := by omega
        rw [Lettered.label_succ _ _ ha, Lettered.label_succ _ _ hb] at hr
        exact Or.inr (Or.inl ⟨a, b, ha, hb, by have := hc.1; omega, hc.2.2, hr, hφ⟩)
    · obtain ⟨s, hs, ht⟩ := hS
      cases s with
      | zero => exact False.elim ht
      | succ a =>
        have ha : a < v.length := by omega
        rw [Lettered.label_succ _ _ ha] at ht
        exact Or.inr (Or.inr ⟨a, ha, ht⟩)
    · obtain ⟨s, hs, hr, hφ⟩ := hS'
      cases s with
      | zero => exact False.elim hr
      | succ a =>
        have ha : a < v.length := by omega
        rw [Lettered.label_succ _ _ ha] at hr
        refine Or.inr (Or.inl ⟨a, j, ha, hj, by omega, ?_, hr, ?_⟩)
        · rw [List.drop_eq_nil_of_le (by omega)]; simp
        · simpa [hlen] using hφ
  · rintro (hF | hR | hT)
    · exact Or.inl (Or.inl hF)
    · obtain ⟨a, b, ha, hb, hab, hc, hr, hφ⟩ := hR
      rcases lt_or_eq_of_le (show b ≤ j by omega) with hbj | rfl
      · refine Or.inr (Or.inl ⟨a + 1, b + 1, ⟨by omega, by omega, hc⟩,
          by omega, ?_, hφ⟩)
        rw [Lettered.label_succ _ _ ha, Lettered.label_succ _ _ hb]
        exact hr
      · refine Or.inr (Or.inr (Or.inr ⟨a + 1, by omega, ?_, ?_⟩))
        · rw [Lettered.label_succ _ _ ha]; exact hr
        · simpa [hlen] using hφ
    · obtain ⟨a, ha, ht⟩ := hT
      rcases lt_or_eq_of_le (show a ≤ j by omega) with haj | rfl
      · refine Or.inr (Or.inr (Or.inl ⟨a + 1, by omega, ?_⟩))
        rw [Lettered.label_succ _ _ ha]; exact ht
      · exact Or.inl (Or.inr ht)

/-- Positive holes of the derived monitor and channel are the block words whose
expansions are positive holes. -/
theorem posHole_der_iff (D : Lettered Γ C) (P : PosChan Γ C) (ℓ : Γ)
    (v : List (List Γ)) (hv : v ≠ []) (hℓ : ∀ X ∈ v, ℓ ∉ X) :
    PosHole (der D ℓ) (posDer D P ℓ) v ↔ PosHole D P (expand ℓ v) :=
  and_congr (isHole_der_iff D ℓ v hv hℓ) (pos_der_iff D P ℓ v hv hℓ)

section Tower
universe u v
variable {α : Type u} {Q : Type v}

/-- The derived channels along a marker sequence. -/
def posTower (D0 : Lettered α Q) (P0 : PosChan α Q) (ℓ : (i : ℕ) → Alph α i) :
    (i : ℕ) → PosChan (Alph α i) (Cores Q i)
  | 0 => P0
  | i + 1 => posDer (tower D0 ℓ i) (posTower D0 P0 ℓ i) (ℓ i)

/-- Only markers strictly below the level affect its positive channel. -/
theorem posTower_congr (D0 : Lettered α Q) (P0 : PosChan α Q)
    {ℓ ℓ' : (i : ℕ) → Alph α i} :
    ∀ j, (∀ t < j, ℓ t = ℓ' t) → posTower D0 P0 ℓ j = posTower D0 P0 ℓ' j
  | 0, _ => rfl
  | i + 1, h => by
      simp only [posTower]
      rw [tower_congr D0 i (fun t ht => h t (by omega)),
        posTower_congr D0 P0 i (fun t ht => h t (by omega)), h i (by omega)]

/-- The positive condition transports through every admissible nonempty level. -/
theorem pos_expandTo_iff (D0 : Lettered α Q) (P0 : PosChan α Q)
    (ℓ : (i : ℕ) → Alph α i) :
    ∀ j (v : List (Alph α j)), Admissible ℓ j v → v ≠ [] →
      (Pos (tower D0 ℓ j) (posTower D0 P0 ℓ j) v ↔ Pos D0 P0 (expandTo ℓ j v))
  | 0, _, _, _ => Iff.rfl
  | j + 1, v, ⟨hav, had⟩, hv => by
      change Pos (der (tower D0 ℓ j) (ℓ j))
        (posDer (tower D0 ℓ j) (posTower D0 P0 ℓ j) (ℓ j)) v ↔ _
      rw [pos_der_iff _ _ _ v hv hav,
        pos_expandTo_iff D0 P0 ℓ j _ had (by simpa [expand_eq_nil] using hv)]
      rfl

/-- The positive holes at level `j` of the towers are the admissible words whose
expansions are positive holes. -/
theorem pos_tower_iff (D0 : Lettered α Q) (P0 : PosChan α Q)
    (ℓ : (i : ℕ) → Alph α i) (j : ℕ) (v : List (Alph α j))
    (had : Admissible ℓ j v) (hv : v ≠ []) :
    PosHole (tower D0 ℓ j) (posTower D0 P0 ℓ j) v ↔ PosHole D0 P0 (expandTo ℓ j v) :=
  and_congr (isHole_tower_iff D0 ℓ j v had hv) (pos_expandTo_iff D0 P0 ℓ j v had hv)

/-- Positive holes at each canonical level are exactly the base positive holes. -/
theorem pos_hierOf_iff [DecidableEq α] [Inhabited α]
    (D0 : Lettered α Q) (P0 : PosChan α Q) {w : List α} (hw : w ≠ []) (i : ℕ) :
    PosHole (tower D0 (markOf w) i) (posTower D0 P0 (markOf w) i) (hierOf w i) ↔
      PosHole D0 P0 w := by
  rw [pos_tower_iff D0 P0 (markOf w) i _ (admissible_hierOf hw i) (hierOf_ne_nil hw i),
    expandTo_hierOf hw i]

end Tower

end DeciENSSE.Anchored
