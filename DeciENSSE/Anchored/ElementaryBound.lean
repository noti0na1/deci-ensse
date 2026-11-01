import DeciENSSE.Anchored.NormalForm
import DeciENSSE.Anchored.Columns
import DeciENSSE.Anchored.Unary
import DeciNSSE.Holes.ElementaryBound

/-! # Elementary anchored compression

In an anchored-normal positive hole the boundary pairs propagate linearly between levels,
so every positive dictionary through the unary top is bounded by `G♯ = 2 + A♯ 3^d`. The top
level is shortened to at most `3 (N + d + 1)` letters, keeping one positive witness, and
supported compression with the positive column automaton shortens every lower level by a
factor `pcolBound (N + d + 1) G♯` while keeping both the derived monitors and channels.
Together these bound the length of a shortest positive hole of depth at most `d` by
`L♯(N, d) = 3 (N + d + 1) · pcolBound (N + d + 1) G♯ ^ d`, independently of the alphabet.
The argument is that of `DeciNSSE.ElementaryBound` and `DeciNSSE.BoundedDepth` for holes,
with the positive channel carried along.

## Main declarations

- `boundary_count_le_of_allowance`, `alphCard_le_of_allowance`: geometric dictionary
  bounds from a per-level allowance.
- `anchoredDictionaryBound`, `exists_bounded_dictionary_posHole`: the dictionary allowance
  `G♯(N, d)`, and positive holes within it.
- `posDescentFactor`, `shorten_pos_level_supported`: positive supported compression of a
  level.
- `exists_short_posHole_of_dictionary`: a short positive hole from bounded dictionaries.
- `anchoredLengthBound`, `exists_short_posHole_elementary`: the length allowance
  `L♯(N, d)`, and short positive holes of bounded depth.
- `Examples.unit_posHole_short`: the hypotheses of `exists_short_posHole_elementary` are
  satisfiable.

The declarations are in the namespace `DeciENSSE.Anchored`.
-/

namespace DeciENSSE.Anchored
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.BoundedDepth

section Count
open DeciNSSE.Exchange DeciNSSE.NormalForm DeciNSSE.HierarchyDepth DeciNSSE.BoundaryPairs
  DeciNSSE.StartCores DeciNSSE.ElementaryBound
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] [Fintype Q] [DecidableEq Q]

/-- If every positive level below the unary top exceeds an allowance `A ≥ 1` by at most
twice its boundary pairs, then twice the boundary pairs at level `i` are at most
`(A - 1) (3 ^ (D - 1 - i) - 1)`, where `D` is the depth. This generalizes
`DeciNSSE.ElementaryBound.normal_boundary_count_le` from the normal allowance to any
allowance, with the same proof. -/
theorem boundary_count_le_of_allowance {w : List α} (hw0 : w ≠ []) {A : ℕ} (hA : 1 ≤ A)
    (hg : ∀ i, 1 ≤ i → i < depth w →
      alphCard w i ≤ A + 2 * (boundaryPairs (hierOf w i)).card)
    {i : ℕ} (hi : 1 ≤ i) (hid : i < depth w) :
    2 * (boundaryPairs (hierOf w i)).card ≤ (A - 1) * (3 ^ (depth w - 1 - i) - 1) := by
  have H : ∀ k i, 1 ≤ i → i + k + 1 = depth w →
      2 * (boundaryPairs (hierOf w i)).card + (A - 1) ≤ (A - 1) * 3 ^ k := by
    intro k
    induction k with
    | zero =>
      intro i hi he
      have hs := boundaryCount_step_add_one hw0 i
      have ht := alphCard_depth_le_one w
      have hb := boundaryPairs_eq_empty_of_isUnary (isUnary_depth w)
      have he' : i + 1 = depth w := by omega
      change _ + 1 ≤ _ + alphCard w (i + 1) at hs
      rw [he', hb, Finset.card_empty] at hs
      simp only [pow_zero, mul_one]
      omega
    | succ k ih =>
      intro i hi he
      have hb := ih (i + 1) (by omega) (by omega)
      have hg' := hg (i + 1) (by omega) (by omega)
      have hs := boundaryCount_step_add_one hw0 i
      change _ + 1 ≤ _ + alphCard w (i + 1) at hs
      rw [pow_succ]
      nlinarith only [hb, hg', hs, Nat.sub_add_cancel hA]
  have h := H (depth w - 1 - i) i hi (by omega)
  rw [Nat.mul_sub_left_distrib, mul_one]
  omega

/-- Under a per-level allowance `A ≥ 1`, the dictionary at a positive level `i` below the
unary top is at most `1 + (A - 1) 3 ^ (D - 1 - i)`. This generalizes
`DeciNSSE.ElementaryBound.normal_alphCard_le` from the normal allowance to any allowance,
with the same proof. -/
theorem alphCard_le_of_allowance {w : List α} (hw0 : w ≠ []) {A : ℕ} (hA : 1 ≤ A)
    (hg : ∀ i, 1 ≤ i → i < depth w →
      alphCard w i ≤ A + 2 * (boundaryPairs (hierOf w i)).card)
    {i : ℕ} (hi : 1 ≤ i) (hid : i < depth w) :
    alphCard w i ≤ 1 + (A - 1) * 3 ^ (depth w - 1 - i) := by
  have hgi := hg i hi hid
  have hb := boundary_count_le_of_allowance hw0 hA hg hi hid
  have hp : 1 ≤ 3 ^ (depth w - 1 - i) := Nat.one_le_pow _ _ (by decide)
  rw [Nat.mul_sub_left_distrib, mul_one] at hb
  have hm := Nat.mul_le_mul_left (A - 1) hp
  simp only [mul_one] at hm
  omega

/-- The anchored dictionary allowance `G♯(N, d)`. -/
def anchoredDictionaryBound (N d : ℕ) : ℕ := 2 + anchoredAllowance N d * 3 ^ d

/-- Every positive hole of depth at most `d` has a positive hole of the same depth and no
greater length whose positive dictionaries are at most `G♯(N, d)`; the positive version of
`DeciNSSE.ElementaryBound.exists_bounded_dictionary_hole`. -/
theorem exists_bounded_dictionary_posHole {D0 : Lettered α Q} {P0 : PosChan α Q}
    {w : List α} {d : ℕ} (hw : PosHole D0 P0 w) (hd : depth w ≤ d) :
    ∃ v, PosHole D0 P0 v ∧ depth v = depth w ∧ v.length ≤ w.length ∧
      ∀ i, 1 ≤ i → i ≤ depth v → alphCard v i ≤ anchoredDictionaryBound (Fintype.card Q) d := by
  obtain ⟨v, hv, hdepth, hlen, _, _, hn⟩ := exists_posNormal_form hw
  refine ⟨v, hv, hdepth, hlen, fun i hi hid => ?_⟩
  have hA : 1 ≤ anchoredAllowance (Fintype.card Q) d := by unfold anchoredAllowance; omega
  rcases eq_or_lt_of_le hid with rfl | hid
  · exact (alphCard_depth_le_one v).trans (by unfold anchoredDictionaryBound; omega)
  · have hg := alphCard_le_of_allowance hv.1.ne_nil hA
      (fun j hj hjd => posNormalAt_alphCard_le hv (hn j hj hjd) hjd (by omega)) hi hid
    refine hg.trans ?_
    unfold anchoredDictionaryBound
    have hp : 3 ^ (depth v - 1 - i) ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := Nat.mul_le_mul (Nat.sub_le (anchoredAllowance (Fintype.card Q) d) 1) hp
    omega

end Count

section Final
open DeciNSSE.HierarchyDepth DeciNSSE.NormalForm DeciNSSE.ElementaryBound
universe u v
variable {α : Type u} {Q : Type v}

/-- More cores do not decrease the number of states of the positive column automaton; the
positive version of `DeciNSSE.BoundedDepth.colBound_mono_core`. -/
theorem pcolBound_mono_core {N M k : ℕ} (hNM : N ≤ M) (hM : 1 ≤ M) :
    pcolBound N k ≤ pcolBound M k := by
  unfold pcolBound
  have h := colBound_mono_core (k := k) hNM hM
  have h2 : ((2 ^ N) ^ (N + 1)) ^ k ≤ ((2 ^ M) ^ (N + 1)) ^ k :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hNM) _) _
  have h3 : ((2 ^ M) ^ (N + 1)) ^ k ≤ ((2 ^ M) ^ (M + 1)) ^ k :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)) _
  have h4 := h2.trans h3
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h h) h4) h4)

/-- The compression factor of one positive level. -/
def posDescentFactor (N d g : ℕ) : ℕ := pcolBound (N + d + 1) g

/-- Positive supported compression of a level `j ≤ d` of a hierarchy with positive
dictionaries at most `g`: every duplicate-free list of level letters has new markers and a
letter map that agree with the towers of monitors and channels on the list, keep it
admissible, and expand each letter to at most `posDescentFactor N d g ^ j` letters. This
follows `DeciNSSE.BoundedDepth.shorten_level_supported`, with the positive column automaton
in place of the column automaton. -/
theorem shorten_pos_level_supported (D0 : Lettered α Q) (P0 : PosChan α Q) [Fintype Q]
    [DecidableEq α] [Inhabited α] {w : List α} (hw : w ≠ [])
    {d g j : ℕ} (hj : j ≤ d) (hg : PositiveDictionaryBound w j g)
    (E : List (Alph α j)) (hE : E.Nodup)
    (hsub : ∀ x ∈ E, x ∈ hierOf w j) :
    ∃ (ℓ' : (i : ℕ) → Alph α i) (φ : Alph α j → Alph α j),
      PosAgree (tower D0 (markOf w) j) (tower D0 ℓ' j)
        (posTower D0 P0 (markOf w) j) (posTower D0 P0 ℓ' j) φ E ∧
      Admissible ℓ' j (E.map φ) ∧
      ∀ x ∈ E, (expandTo ℓ' j [φ x]).length ≤ posDescentFactor (Fintype.card Q) d g ^ j := by
  classical
  induction j with
  | zero =>
      exact ⟨markOf w, id, PosAgree.refl _ _ _, trivial, fun x _ => by simp [expandTo]⟩
  | succ j ih =>
      let ℓ := markOf w
      have hadm : Admissible ℓ (j + 1) E :=
        admissible_of_subset ℓ (j + 1) E _ (admissible_hierOf hw _)
          (hierOf_ne_nil hw _) hsub
      set N := Fintype.card Q with hN
      set D := tower D0 ℓ j with hD
      obtain ⟨ψ, hψA, hψ⟩ := exists_short_pos_letters D (posTower D0 P0 ℓ j) (ℓ j) g E
        (length_le_of_dictionaryBound hg hE hsub)
      rw [card_cores j] at hψ
      set Ebig : List (Alph α j) := (ℓ j :: (E.map ψ).flatten).dedup with hEbig
      have hmemBig : ∀ X ∈ E, ∀ a ∈ ψ X, a ∈ Ebig := fun X hX a ha =>
        List.mem_dedup.mpr (List.mem_cons_of_mem _
          (List.mem_flatten.mpr ⟨ψ X, List.mem_map_of_mem hX, ha⟩))
      have hℓBig : ℓ j ∈ Ebig := List.mem_dedup.mpr List.mem_cons_self
      have hsubBig : ∀ a ∈ Ebig, a ∈ hierOf w j := by
        intro a ha
        rcases List.mem_cons.mp (List.mem_dedup.mp ha) with rfl | ha
        · exact markOf_mem hw j
        · obtain ⟨Y, hY, haY⟩ := List.mem_flatten.mp ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact mem_lower_dictionary hw (hsub X hX) ((hψ X hX).1.subset haY)
      obtain ⟨ℓ'', φ₀, hA, hadm'', hsize⟩ :=
        ih (by omega) (fun t ht htd => hg t ht (by omega)) Ebig
          (List.nodup_dedup _) hsubBig
      set ℓ' : (i : ℕ) → Alph α i := Function.update ℓ'' j (φ₀ (ℓ j)) with hℓ'
      have hℓ'j : ℓ' j = φ₀ (ℓ j) := Function.update_self _ _ _
      have hℓ'lt : ∀ t < j, ℓ' t = ℓ'' t := fun t ht =>
        Function.update_of_ne (by omega) _ _
      have htw : tower D0 ℓ' j = tower D0 ℓ'' j := tower_congr D0 j hℓ'lt
      have htw1 : tower D0 ℓ' (j + 1) = der (tower D0 ℓ'' j) (φ₀ (ℓ j)) := by
        show der (tower D0 ℓ' j) (ℓ' j) = _
        rw [htw, hℓ'j]
      have hptw : posTower D0 P0 ℓ' j = posTower D0 P0 ℓ'' j :=
        posTower_congr D0 P0 j hℓ'lt
      have hptw1 : posTower D0 P0 ℓ' (j + 1) =
          posDer (tower D0 ℓ'' j) (posTower D0 P0 ℓ'' j) (φ₀ (ℓ j)) := by
        change posDer (tower D0 ℓ' j) (posTower D0 P0 ℓ' j) (ℓ' j) = _
        rw [htw, hptw, hℓ'j]
      refine ⟨ℓ', fun X => (ψ X).map φ₀, ?_, ?_, ?_⟩
      · rw [htw1, hptw1]
        exact hψA.comp (hA.derive hℓBig (E.map ψ) (by
          intro Y hY a ha
          obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
          exact hmemBig X hX a ha))
      · exact admissible_update_map ℓ'' φ₀ hℓBig
          (fun a ha h => hA.neg.inj a ha (ℓ j) hℓBig h)
          hadm'' ψ hmemBig (fun X hX h => hadm.1 X hX ((hψ X hX).1.subset h))
      · intro X hX
        refine (length_expandTo_update_le ℓ'' φ₀ (ℓ j) (ψ X)
          (B := posDescentFactor N d g ^ j) fun y hy => hsize y ?_).trans ?_
        · rcases List.mem_append.mp hy with h1 | h1
          · exact hmemBig X hX y h1
          · rw [List.mem_singleton.mp h1]
            exact hℓBig
        · rw [pow_succ']
          apply Nat.mul_le_mul_right
          exact (hψ X hX).2.trans_le (pcolBound_mono_core (by omega) (by omega))

/-- A positive hole with a unary level `i ≤ d` and positive dictionaries at most `g` has a
positive hole of depth at most `d` and length at most
`3 (N + d + 1) · posDescentFactor N d g ^ d`. This follows
`DeciNSSE.BoundedDepth.exists_short_hole_of_dictionary`; the factor `3` comes from the
positive unary shortening `unary_posHole_shorten`. -/
theorem exists_short_posHole_of_dictionary [DecidableEq α] [Inhabited α]
    (D0 : Lettered α Q) (P0 : PosChan α Q) [Fintype Q]
    {w : List α} {i d g : ℕ} (hw : PosHole D0 P0 w) (hi : i ≤ d)
    (hu : IsUnary (hierOf w i)) (hg : PositiveDictionaryBound w i g) :
    ∃ v, PosHole D0 P0 v ∧ InL d v ∧
      v.length ≤ 3 * (Fintype.card Q + d + 1) *
        posDescentFactor (Fintype.card Q) d g ^ d := by
  classical
  have hw0 : w ≠ [] := hw.1.ne_nil
  set N := Fintype.card Q with hN
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hierOf_ne_nil hw0 i)
  have hrep : hierOf w i = List.replicate (hierOf w i).length x :=
    List.eq_replicate_iff.mpr ⟨rfl, fun b hb => hu b hb x hx⟩
  have hv := (pos_hierOf_iff D0 P0 hw0 i).mpr hw
  rw [hrep] at hv
  obtain ⟨m, -, hmN, hm⟩ := unary_posHole_shorten _ _ x hv
  rw [card_cores i] at hmN
  obtain ⟨ℓ', φ, hA, hadm', hsize⟩ :=
    shorten_pos_level_supported D0 P0 hw0 hi hg [x] (by simp)
      (fun a ha => by rw [List.mem_singleton.mp ha]; exact hx)
  have hv' : PosHole (tower D0 ℓ' i) (posTower D0 P0 ℓ' i) (List.replicate m (φ x)) := by
    rw [← List.map_replicate]
    exact (hA.posHole_iff fun a ha =>
      List.mem_singleton.mpr (List.eq_of_mem_replicate ha)).mpr hm
  have hadm₂ : Admissible ℓ' i (List.replicate m (φ x)) :=
    admissible_of_subset ℓ' i _ _ hadm' (by simp) fun a ha => by
      rw [List.eq_of_mem_replicate ha]; exact List.mem_map_of_mem (List.mem_singleton_self x)
  refine ⟨expandTo ℓ' i (List.replicate m (φ x)),
    (pos_tower_iff D0 P0 ℓ' i _ hadm₂ hv'.1.ne_nil).mp hv', ⟨i, hi, ?_⟩, ?_⟩
  · rw [(hierOf_expandTo ℓ' i _ hadm₂ hv'.1.ne_nil).1]
    intro a ha b hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  · have hm3 : m ≤ 3 * (N + i) := hmN.trans (min_le_right _ _)
    calc (expandTo ℓ' i (List.replicate m (φ x))).length
          ≤ (List.replicate m (φ x)).length * posDescentFactor N d g ^ i :=
          length_expandTo_le ℓ' i _ fun z hz => by
            rw [List.eq_of_mem_replicate hz]; exact hsize x (List.mem_singleton_self x)
      _ ≤ (3 * (N + i)) * posDescentFactor N d g ^ i := by
          rw [List.length_replicate]; exact Nat.mul_le_mul_right _ hm3
      _ ≤ 3 * (N + d + 1) * posDescentFactor N d g ^ d := by
          apply Nat.mul_le_mul (by omega)
          apply Nat.pow_le_pow_right
          · unfold posDescentFactor pcolBound colBound
            positivity
          · exact hi

/-- The anchored length allowance `L♯(N, d)`. -/
def anchoredLengthBound (N d : ℕ) : ℕ :=
  3 * (N + d + 1) * posDescentFactor N d (anchoredDictionaryBound N d) ^ d

/-- Elementary anchored compression: a positive hole of depth at most `d` of a monitor with
`N` cores has a positive hole of depth at most `d` and length at most `L♯(N, d)`. -/
theorem exists_short_posHole_elementary [DecidableEq α] [Inhabited α] [Fintype Q]
    {D0 : Lettered α Q} {P0 : PosChan α Q} {w : List α} {d : ℕ}
    (hw : PosHole D0 P0 w) (hL : InL d w) :
    ∃ v, PosHole D0 P0 v ∧ InL d v ∧ v.length ≤ anchoredLengthBound (Fintype.card Q) d := by
  classical
  obtain ⟨i, hi, hu⟩ := hL
  have hd : depth w ≤ d := (Nat.find_min' (exists_isUnary_hierOf w) hu).trans hi
  obtain ⟨v, hv, hdepth, _, hg⟩ := exists_bounded_dictionary_posHole hw hd
  exact exists_short_posHole_of_dictionary D0 P0 hv (hdepth ▸ hd) (isUnary_depth v) hg

end Final

namespace Examples

/-- A monitor with one core that admits nothing and accepts every final letter. -/
def unitMonitor : Lettered Bool Unit :=
  ⟨(), fun _ _ => (), fun _ _ => False, fun _ _ => False, fun _ _ => True⟩

/-- A channel whose final test always holds. -/
def unitChannel : PosChan Bool Unit :=
  ⟨fun _ _ => True, fun _ _ => False, fun _ _ => False, fun _ _ => False, fun _ => False⟩

/-- The hypotheses of `exists_short_posHole_elementary` are satisfiable: the one-letter word
`[true]` is a positive hole of depth zero. -/
theorem unit_posHole_short :
    ∃ v, PosHole unitMonitor unitChannel v ∧ InL 0 v ∧ v.length ≤ anchoredLengthBound 1 0 := by
  have hw : PosHole unitMonitor unitChannel [true] :=
    ⟨⟨⟨(), true, rfl, trivial⟩, fun _ _ h => h, fun _ _ _ _ h => h⟩,
      Or.inl ⟨(), true, rfl, trivial⟩⟩
  obtain ⟨v, hv, hL, hlen⟩ := exists_short_posHole_elementary hw
    ⟨0, le_rfl, fun a ha b hb => by simp_all [hierOf]⟩
  exact ⟨v, hv, hL, by simpa using hlen⟩

end Examples

end DeciENSSE.Anchored
