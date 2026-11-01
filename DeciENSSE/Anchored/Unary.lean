import DeciENSSE.Anchored.Channel
import DeciNSSE.Holes.Hierarchy.Unary

/-! # Positive unary holes

Every pair of cuts of a power `x^m` is a comparison with continuation letter `x`, and its
labels follow the orbit of the start core under `x`. Deleting a loop between two cuts with
equal labels keeps a hole, and keeps a positive witness when no cut of the witness is
deleted. Protecting the at most three cuts of one witness leaves at most three stretches of
pairwise distinct labels, so a positive unary hole has one of length at most `3 |C|`.

## Main declarations

- `unaryLabel`, `label_replicate`, `pos_replicate_iff`: labels and the positive condition
  of a power.
- `unary_pos_shorten`: shortening a positive power while keeping its final label.
- `unary_posHole_shorten`: a positive unary hole of length at most `3 |C|`.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

variable {Γ C : Type*}

/-- The label at a unary cut, independent of the total word length. -/
def unaryLabel (D : Lettered Γ C) (x : Γ) : ℕ → Lab Γ C
  | 0 => none
  | k + 1 => some ((D.κ x)^[k] D.start, x)

/-- The labels of a power are its unary labels. -/
theorem label_replicate (D : Lettered Γ C) (x : Γ) {m k : ℕ} (hk : k ≤ m) :
    D.label (List.replicate m x) k = unaryLabel D x k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Lettered.label_succ _ _ (by simp; omega),
      core_replicate D x m k (by omega)]
    simp [unaryLabel]

/-- Every ordered pair of cuts in a unary word is a comparison. -/
theorem isComp_replicate (x : Γ) {m s e : ℕ} (hse : s < e) (he : e ≤ m) :
    IsComp (List.replicate m x) s e := by
  refine ⟨hse, by simpa, ?_⟩
  rw [List.drop_replicate, List.drop_replicate,
    show m - s = (m - e) + (e - s) by omega, List.replicate_add]
  exact List.prefix_append _ _

/-- A letter test on a power tests its letter inside the word. -/
theorem at_replicate_iff (Φ : Γ → Prop) (x : Γ) (m i : ℕ) :
    At Φ (List.replicate m x) i ↔ i < m ∧ Φ x := by
  by_cases hi : i < m
  · simp [At, hi]
  · simp [At, hi]

/-- On a unary word the continuation test is just the letter predicate. -/
theorem pos_replicate_iff (D : Lettered Γ C) (P : PosChan Γ C) (x : Γ) (m : ℕ) :
    Pos D P (List.replicate m x) ↔
      (∃ c a, unaryLabel D x m = some (c, a) ∧ P.F c a) ∨
      (∃ s e, s < e ∧ e < m ∧ P.R (unaryLabel D x s) (unaryLabel D x e) ∧ P.Φ x) ∨
      (∃ s < m, P.S (unaryLabel D x s) (unaryLabel D x m)) ∨
      (∃ s < m, P.S' (unaryLabel D x s) (unaryLabel D x m) ∧ P.Φ x) := by
  rw [Pos]
  simp only [List.length_replicate]
  apply or_congr
  · rw [label_replicate D x le_rfl]
  apply or_congr
  · constructor
    · rintro ⟨s, e, hc, he, hr, hφ⟩
      rw [label_replicate D x (by have := hc.1; omega), label_replicate D x he.le] at hr
      exact ⟨s, e, hc.1, he, hr, (at_replicate_iff _ _ _ _).mp hφ |>.2⟩
    · rintro ⟨s, e, hse, he, hr, hφ⟩
      refine ⟨s, e, isComp_replicate x hse he.le, he, ?_, ?_⟩
      · rwa [label_replicate D x (by omega), label_replicate D x he.le]
      · exact (at_replicate_iff _ _ _ _).mpr ⟨by omega, hφ⟩
  apply or_congr
  · apply exists_congr; intro s
    apply and_congr_right; intro hs
    rw [label_replicate D x hs.le, label_replicate D x le_rfl]
  · apply exists_congr; intro s
    apply and_congr_right; intro hs
    rw [label_replicate D x hs.le, label_replicate D x le_rfl, at_replicate_iff]
    simp [hs]

/-- A unary prefix with the same final label inherits holehood. -/
theorem unary_hole_prefix (D : Lettered Γ C) (x : Γ) {m n : ℕ}
    (hm : D.IsHole (List.replicate m x)) (hn : n ≤ m)
    (hfin : unaryLabel D x n = unaryLabel D x m) :
    D.IsHole (List.replicate n x) := by
  obtain ⟨⟨c, a, hl, hT⟩, hE, hI⟩ := hm
  unfold Lettered.IsHole
  simp only [List.length_replicate] at hl hE hI ⊢
  rw [label_replicate D x le_rfl] at hl
  refine ⟨⟨c, a, ?_, hT⟩, fun s hs => ?_, fun s e hc he => ?_⟩
  · rwa [label_replicate D x le_rfl, hfin]
  · have h := hE s (by omega)
    rwa [label_replicate D x (by omega), label_replicate D x le_rfl,
      ← hfin, ← label_replicate D x hs.le, ← label_replicate D x le_rfl] at h
  · have h := hI s e (isComp_replicate x hc.1 (by omega)) (by omega)
    rw [label_replicate D x (by have := hc.1; omega),
      label_replicate D x (by omega)] at h
    rwa [label_replicate D x (by have := hc.1; omega), label_replicate D x he.le]

/-- After a protected cut `a`, the label at a later cut recurs within `|C|` letters, at a
cut after `a`. -/
theorem unary_cut_small_after [Fintype C] (D : Lettered Γ C) (x : Γ)
    {a b : ℕ} (hab : a < b) :
    ∃ b', a < b' ∧ b' ≤ b ∧ b' ≤ a + Fintype.card C ∧
      unaryLabel D x b' = unaryLabel D x b := by
  obtain ⟨t, ht, htC, hte⟩ :=
    iterate_small (D.κ x) ((D.κ x)^[a] D.start) (b - 1 - a)
  refine ⟨a + t + 1, by omega, by omega, by omega, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  simp only [unaryLabel]
  congr 2
  have hk : k = (k - a) + a := by omega
  rw [Nat.add_comm a t, Function.iterate_add_apply, hk]
  simpa only [Nat.add_sub_cancel, Function.iterate_add_apply] using hte

/-- The label at a cut recurs within `|C|` letters; a positive cut stays positive. -/
theorem unary_cut_small [Fintype C] (D : Lettered Γ C) (x : Γ) (s : ℕ) :
    ∃ s', s' ≤ s ∧ s' ≤ Fintype.card C ∧ unaryLabel D x s' = unaryLabel D x s := by
  cases s with
  | zero => exact ⟨0, le_rfl, Nat.zero_le _, rfl⟩
  | succ s =>
    obtain ⟨s', _, hs, hN, hl⟩ := unary_cut_small_after D x (a := 0) (b := s + 1) (by omega)
    exact ⟨s', hs, by simpa using hN, hl⟩

/-- Shorten the positive witness cuts first and the final cut last. The
nonterminal `R` case uses three orbit segments, the other cases at most two. -/
theorem unary_pos_shorten [Fintype C] (D : Lettered Γ C) (P : PosChan Γ C)
    (x : Γ) {m : ℕ} (hm : 1 ≤ m) (hp : Pos D P (List.replicate m x)) :
    ∃ n, 1 ≤ n ∧ n ≤ min m (3 * Fintype.card C) ∧
      unaryLabel D x n = unaryLabel D x m ∧ Pos D P (List.replicate n x) := by
  rw [pos_replicate_iff] at hp
  rcases hp with hF | ⟨s, e, hse, he, hR, hφ⟩ | ⟨s, hs, hS⟩ | ⟨s, hs, hS, hφ⟩
  · obtain ⟨n, hn, hnm, hnC, hl⟩ := unary_cut_small_after D x (a := 0) (b := m) (by omega)
    refine ⟨n, by omega, le_min hnm (by omega), hl, ?_⟩
    rw [pos_replicate_iff]
    exact Or.inl (hl.symm ▸ hF)
  · obtain ⟨s', hss, hsC, hsl⟩ := unary_cut_small D x s
    obtain ⟨e', hse', hee, heC, hel⟩ := unary_cut_small_after D x (a := s') (b := e) (by omega)
    obtain ⟨n, hen, hnm, hnC, hl⟩ := unary_cut_small_after D x (a := e') (b := m) (by omega)
    refine ⟨n, by omega, le_min hnm (by omega), hl, ?_⟩
    rw [pos_replicate_iff]
    exact Or.inr (Or.inl ⟨s', e', hse', hen, by rwa [hsl, hel], hφ⟩)
  · obtain ⟨s', hss, hsC, hsl⟩ := unary_cut_small D x s
    obtain ⟨n, hsn, hnm, hnC, hl⟩ := unary_cut_small_after D x (a := s') (b := m) (by omega)
    refine ⟨n, by omega, le_min hnm (by omega), hl, ?_⟩
    rw [pos_replicate_iff]
    exact Or.inr (Or.inr (Or.inl ⟨s', hsn, by rwa [hsl, hl]⟩))
  · obtain ⟨s', hss, hsC, hsl⟩ := unary_cut_small D x s
    obtain ⟨n, hsn, hnm, hnC, hl⟩ := unary_cut_small_after D x (a := s') (b := m) (by omega)
    refine ⟨n, by omega, le_min hnm (by omega), hl, ?_⟩
    rw [pos_replicate_iff]
    exact Or.inr (Or.inr (Or.inr ⟨s', hsn, by rwa [hsl, hl], hφ⟩))

/-- Every positive unary hole `x^m` has a positive unary hole `x^n` with
`1 ≤ n ≤ min m (3 |C|)`. -/
theorem unary_posHole_shorten [Fintype C] (D : Lettered Γ C) (P : PosChan Γ C)
    (x : Γ) {m : ℕ} (hm : PosHole D P (List.replicate m x)) :
    ∃ n, 1 ≤ n ∧ n ≤ min m (3 * Fintype.card C) ∧ PosHole D P (List.replicate n x) := by
  have hm0 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    exact hm.1.ne_nil (by simp [this])
  obtain ⟨n, hn, hnm, hl, hp⟩ := unary_pos_shorten D P x hm0 hm.2
  exact ⟨n, hn, hnm, unary_hole_prefix D x hm.1 (le_trans hnm (min_le_left _ _)) hl, hp⟩

end DeciENSSE.Anchored
