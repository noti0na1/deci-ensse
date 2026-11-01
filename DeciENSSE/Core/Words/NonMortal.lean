import DeciENSSE.Core.Words.Streams
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import DeciENSSE.Core.Words.Transport

/-! # Safe paths and non-mortal continuations

Safe paths split into mortal, branching, and thin cases. A hole decomposes into a
pre-hole and a safe continuation. Bounded lassos describe thin continuations, and
survivor-free streams supply finite completions.

## Main declarations

- `TwoWordInstance.hole_decomposition`: factor a hole at its first rejected cut.
- `TwoWordInstance.state_kinds`: classify safe states.
- `TwoWordInstance.thin_lasso_iff`: characterize thin safe streams by bounded lassos.
- `TwoWordInstance.survivorFree_completes`: complete a survivor-free pre-hole.
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

variable {α : Type*} [Inhabited α]

namespace TwoWordInstance
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : TwoWordInstance α SA SB SA' SB')

section FinitePaths
omit [Inhabited α]

/-- Natural offset, used only for cross comparisons (where it is nonnegative). -/
def offset (u t : Word α) (s e : ℕ) : ℕ := (u.length - s) - (t.length - e)

/-- The part of the spine suffix beyond the target suffix. -/
def overhang (u t : Word α) (s e : ℕ) : Word α := (u.drop s).drop (t.length - e)

/-- A cross comparison factors the spine suffix into target suffix and overhang. -/
theorem cross_factor {u t : Word α} {s e : ℕ} (h : Cross u t s e) :
    u.drop s = t.drop e ++ overhang u t s e := by
  obtain ⟨z, hz⟩ := h.2.2
  simp [overhang, ← hz]

/-- The overhang length is the difference between the compared suffix lengths. -/
theorem overhang_length (u t : Word α) (s e : ℕ) :
    (overhang u t s e).length = offset u t s e := by simp [overhang, offset, Nat.sub_sub]

/-- A cross comparison bounds the offset by the spine length. -/
theorem cross_offset_le {u t : Word α} {s e : ℕ} (_h : Cross u t s e) :
    offset u t s e ≤ u.length := by
  unfold offset; omega

/-- A cross comparison is aligned exactly when its overhang is empty. -/
theorem cross_aligned_iff {u t : Word α} {s e : ℕ} (h : Cross u t s e) :
    Aligned u t s e ↔ overhang u t s e = [] := by
  rw [Aligned, and_iff_right h.1, and_iff_right h.2.1, cross_factor h]
  simp

/-- The finite self-overlap condition for keeping a comparison. -/
def Keeps (u t : Word α) (s e : ℕ) (θ : Word α) : Prop :=
  θ.IsPrefix (overhang u t s e ++ θ)

/-- Safety is absence of bad states at every cut of the run. -/
theorem safeFrom_iff {q : SA} {w : Word α} :
    I.SafeFrom q w ↔ ∀ s ≤ w.length, I.A.runFrom q (w.take s) ∉ I.Bad := by
  simp [SafeFrom, Nat.lt_succ_iff]

/-- A safe word starts in a nonbad state. -/
theorem safeFrom_start {q : SA} {w : Word α} (h : I.SafeFrom q w) : q ∉ I.Bad := by
  simpa using (I.safeFrom_iff.mp h) 0 (Nat.zero_le _)

/-- A safe word ends in a nonbad state. -/
theorem safeFrom_end {q : SA} {w : Word α} (h : I.SafeFrom q w) :
    I.A.runFrom q w ∉ I.Bad := by
  simpa using (I.safeFrom_iff.mp h) w.length le_rfl

/-- Safety of concatenation splits into safety of the two runs. -/
theorem safeFrom_append {q : SA} {u v : Word α} :
    I.SafeFrom q (u ++ v) ↔ I.SafeFrom q u ∧ I.SafeFrom (I.A.runFrom q u) v := by
  simp only [safeFrom_iff]
  constructor
  · intro h
    constructor
    · intro s hs
      simpa [List.take_append_of_le_length hs] using h s (by simp; omega)
    · intro s hs
      simpa [List.take_append, List.take_of_length_le (Nat.le_add_right u.length s),
        LDFA.runFrom_append] using
        h (u.length + s) (by simp; omega)
  · rintro ⟨hu, hv⟩ s hs
    by_cases hsu : s ≤ u.length
    · simpa [List.take_append_of_le_length hsu] using hu s hsu
    · simpa [List.take_append, List.take_of_length_le (by omega : u.length ≤ s),
        LDFA.runFrom_append] using hv (s - u.length) (by simp at hs; omega)

/-- Every prefix of a safe word is safe. -/
theorem safeFrom_prefix {q : SA} {u v : Word α} (h : I.SafeFrom q v)
    (hp : u.IsPrefix v) : I.SafeFrom q u := by
  obtain ⟨z, rfl⟩ := hp
  exact (I.safeFrom_append.mp h).1

/-- Every finite prefix of an infinitely safe stream is safe. -/
theorem infiniteSafe_prefix {q : SA} {ξ : ℕ → α} (h : I.InfiniteSafe q ξ) (n : ℕ) :
    I.SafeFrom q (streamPrefix ξ n) := by
  apply I.safeFrom_iff.mpr
  intro s hs
  simpa [streamPrefix_take ξ (by simpa using hs),
    ← LDFA.streamRun_eq] using h s

/-- A safe finite word may be prepended to an infinitely safe continuation. -/
theorem infiniteSafe_prepend {q : SA} {w : Word α} {ξ : ℕ → α}
    (hw : I.SafeFrom q w) (hξ : I.InfiniteSafe (I.A.runFrom q w) ξ) :
    I.InfiniteSafe q (prepend w ξ) := by
  intro n
  by_cases hn : n ≤ w.length
  · have ht : streamPrefix (prepend w ξ) n = w.take n := by
      have := streamPrefix_take (prepend w ξ) hn
      simpa [prepend_prefix] using this.symm
    simpa [LDFA.streamRun_eq, ht] using (I.safeFrom_iff.mp hw) n hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : w.length ≤ n)
    simpa [LDFA.streamRun_prepend] using hξ k

/-- Appending a word preserves an existing first rejected cut. -/
theorem J_append {t : Word α} {j : ℕ} (hj : I.J t = some j) (θ : Word α) :
    I.J (t ++ θ) = some j := by
  obtain ⟨hr, hl, hmin⟩ := (I.J_eq_some_iff t j).mp hj
  apply (I.J_eq_some_iff _ _).mpr
  refine ⟨?_, by simp; omega, ?_⟩
  · simpa [LDFA.atCut_append _ _ _ hl] using hr
  · intro i hi
    simpa [LDFA.atCut_append _ _ _ (by omega : i ≤ t.length)] using hmin i hi

/-- A common finite suffix can be canceled from this prefix comparison. -/
theorem prefix_append_cancel_common {x y θ : Word α}
    (h : (y ++ θ).IsPrefix (x ++ θ)) : y.IsPrefix x := by
  have hlen := h.length_le
  have hy : y.IsPrefix (x ++ θ) := (List.prefix_append y θ).trans h
  exact (List.isPrefix_append_of_length (by simp at hlen; omega)).mp hy

/-- Extending both words preserves a cross comparison exactly when it is kept. -/
theorem cross_append_iff {u t θ : Word α} {s e : ℕ} (he : e ≤ t.length) :
    Cross (u ++ θ) (t ++ θ) s e ↔ Cross u t s e ∧ Keeps u t s e θ := by
  constructor
  · intro h
    have hl := h.2.2.length_le
    simp only [List.length_drop, List.length_append] at hl
    have hs : s ≤ u.length := by
      have hb := h.1
      simp only [List.length_append] at hb
      omega
    have hd : (t.drop e ++ θ).IsPrefix (u.drop s ++ θ) := by
      simpa [List.drop_append_of_le_length hs, List.drop_append_of_le_length he] using h.2.2
    have hc : Cross u t s e := ⟨hs, he, prefix_append_cancel_common hd⟩
    refine ⟨hc, ?_⟩
    rw [cross_factor hc, List.append_assoc, List.prefix_append_right_inj] at hd
    exact hd
  · rintro ⟨hc, hk⟩
    refine ⟨by have := hc.1; simp; omega, by simp; omega, ?_⟩
    rw [List.drop_append_of_le_length hc.1, List.drop_append_of_le_length he,
      cross_factor hc, List.append_assoc, List.prefix_append_right_inj]
    exact hk

/-- Even cuts introduced in the continuation cannot create events. -/
theorem event_append_iff {u t θ : Word α} {s e j : ℕ} (hj : I.J t = some j) :
    I.Event (u ++ θ) (t ++ θ) s e ↔ I.Event u t s e ∧ Keeps u t s e θ := by
  have hja := I.J_append hj θ
  have hjl := ((I.J_eq_some_iff t j).mp hj).2.1
  constructor
  · rintro ⟨hc, ⟨j', hj', he⟩, hg⟩
    have hj'e : j' = j := by
      have hh : j = j' := by simpa [hja] using hj'
      exact hh.symm
    subst j'
    obtain ⟨hc, hk⟩ := (cross_append_iff (le_trans he hjl)).mp hc
    refine ⟨⟨hc, ⟨j, by simp [hj], he⟩, ?_⟩, hk⟩
    simpa [LDFA.atCut_append _ _ _ hc.1,
      LDFA.atCut_append _ _ _ hc.2.1] using hg
  · rintro ⟨⟨hc, he, hg⟩, hk⟩
    refine ⟨(cross_append_iff hc.2.1).mpr ⟨hc, hk⟩, ?_, ?_⟩
    · simpa [hja, hj] using he
    · simpa [LDFA.atCut_append _ _ _ hc.1,
        LDFA.atCut_append _ _ _ hc.2.1] using hg

/-- Aligned comparisons are kept by every word. -/
theorem aligned_keeps {u t : Word α} {s e : ℕ} (h : Aligned u t s e) (θ : Word α) :
    Keeps u t s e θ := by
  have hc : Cross u t s e := ⟨h.1, h.2.1, h.2.2 ▸ List.prefix_rfl⟩
  simp [Keeps, (cross_aligned_iff hc).mp h]

/-- Keeping a comparison is preserved by taking a prefix of the continuation. -/
theorem keeps_prefix {u t θ ψ : Word α} {s e : ℕ}
    (h : Keeps u t s e ψ) (hp : θ.IsPrefix ψ) : Keeps u t s e θ := by
  obtain ⟨z, rfl⟩ := hp
  unfold Keeps at *
  have hθ := (List.prefix_append θ z).trans h
  rw [← List.append_assoc] at hθ
  exact (List.isPrefix_append_of_length (by simp)).mp hθ

/-- Extending both words equally preserves each head event. -/
theorem headEvent_append {u t : Word α} {s e : ℕ} (h : I.HeadEvent u t s e) (θ : Word α) :
    I.HeadEvent (u ++ θ) (t ++ θ) s e := by
  refine ⟨⟨by have := h.1.1; simp; omega,
    by have := h.1.2.1; simp; omega, ?_⟩, ?_⟩
  · simp [List.drop_append_of_le_length h.1.1,
      List.drop_append_of_le_length h.1.2.1, h.1.2.2]
  · simpa [LDFA.atCut_append _ _ _ h.1.1,
      LDFA.atCut_append _ _ _ h.1.2.1] using h.2

/-- A head event is preserved by extending both words equally. -/
theorem hasHeadEvent_append {u t : Word α} (h : I.HasHeadEvent u t) (θ : Word α) :
    I.HasHeadEvent (u ++ θ) (t ++ θ) := by
  obtain ⟨s, hs, e, he, hh⟩ := h
  refine ⟨s, ?_, e, ?_, I.headEvent_append hh θ⟩ <;>
    simp only [Finset.mem_range, List.length_append] at * <;> omega

/-- A continuation that completes an `IsPreHole` by eliminating its surviving events. -/
def Completes (u t θ : Word α) : Prop := I.SafeFrom (I.A.run u) θ ∧
  ∀ s e, I.Event u t s e → ¬ Keeps u t s e θ

/-- Completing a pre-hole produces a hole. -/
theorem preHole_complete {u t θ : Word α} (hp : I.IsPreHole u t)
    (hθ : I.Completes u t θ) : I.IsHole (u ++ θ) (t ++ θ) := by
  refine ⟨I.safeFrom_append.mpr ⟨hp.1, hθ.1⟩, ?_, ?_, I.hasHeadEvent_append hp.2.2.1 θ⟩
  · simp [I.J_append hp.2.1 θ]
  · intro s _ e _ he
    obtain ⟨he, hk⟩ := (I.event_append_iff hp.2.1).mp he
    exact hθ.2 s e he hk

/-- ForcedHeads puts every head cut before the first rejection. -/
theorem head_cut_le_J {u t : Word α} {s e j : ℕ} (hf : I.ForcedHeads)
    (hh : I.HeadEvent u t s e) (hj : I.J t = some j) : e ≤ j := by
  by_contra hn
  have he := hh.1.2.1
  have hproper : j < (t.take e).length := by simp; omega
  have hnrej := hf _ _ hh.2 ⟨u.take s, rfl⟩ (t.take e) rfl j hproper
  have hr := ((I.J_eq_some_iff t j).mp hj).1
  apply hnrej
  simpa [LDFA.atCut, List.take_take, Nat.min_eq_left (by omega : j ≤ e)] using hr

/-- A rejection found in the first word determines the first cut after extension. -/
theorem J_of_append {t θ : Word α} {j : ℕ} (hj : I.J (t ++ θ) = some j)
    (hl : j ≤ t.length) : I.J t = some j := by
  obtain ⟨hr, _, hm⟩ := (I.J_eq_some_iff _ _).mp hj
  apply (I.J_eq_some_iff _ _).mpr
  refine ⟨?_, hl, ?_⟩
  · simpa [LDFA.atCut_append _ _ _ hl] using hr
  · intro i hi
    simpa [LDFA.atCut_append _ _ _ (by omega : i ≤ t.length)] using hm i hi

/-- Reverse continuation calculation once the head and rejection cuts are retained. -/
theorem preHole_of_completed_hole {u t θ : Word α} (hh : I.IsHole (u ++ θ) (t ++ θ))
    (hj : I.J t = some t.length) (hd : I.HasHeadEvent u t) :
    I.IsPreHole u t ∧ I.Completes u t θ := by
  have hs := I.safeFrom_append.mp hh.1
  have hb : ∀ s e, I.Event u t s e → ¬ Keeps u t s e θ := by
    intro s e he hk
    have hev := (I.event_append_iff hj).mpr ⟨he, hk⟩
    exact hh.2.2.1 s (Finset.mem_range.mpr (by have := hev.1.1; omega))
      e (Finset.mem_range.mpr (by have := hev.1.2.1; omega)) hev
  refine ⟨⟨hs.1, hj, hd, ?_⟩, hs.2, hb⟩
  intro s _ e _ ⟨he, ha⟩
  exact hb s e he (aligned_keeps ha θ)

/-- Every hole decomposes at its first rejected cut into a pre-hole and a completion. -/
theorem hole_decomposition {u t : Word α} (hf : I.ForcedHeads) (hh : I.IsHole u t) :
    ∃ u₀ t₀ θ, u = u₀ ++ θ ∧ t = t₀ ++ θ ∧ θ = t.drop t₀.length ∧
      I.IsPreHole u₀ t₀ ∧ I.Completes u₀ t₀ θ := by
  obtain ⟨j, hj⟩ : ∃ j, I.J t = some j := Option.isSome_iff_exists.mp hh.2.1
  obtain ⟨s, _, e, _, hd⟩ := hh.2.2.2
  have hs := hd.1.1
  have he := hd.1.2.1
  have hej := I.head_cut_le_J hf hd hj
  have hjt := ((I.J_eq_some_iff t j).mp hj).2.1
  let β := u.take s
  let γ := t.take e
  let σ := t.drop e
  have hu : u = β ++ σ := by simp [β, σ, ← hd.1.2.2]
  have ht : t = γ ++ σ := (List.take_append_drop e t).symm
  let u₀ := β ++ σ.take (j - e)
  let t₀ := γ ++ σ.take (j - e)
  let θ := σ.drop (j - e)
  have hsplitu : u = u₀ ++ θ := by simp [u₀, θ, List.append_assoc, hu]
  have hsplitt : t = t₀ ++ θ := by simp [t₀, θ, List.append_assoc, ht]
  have htl : t₀.length = j := by
    simp only [t₀, γ, σ, List.length_append, List.length_take, List.length_drop]
    omega
  have hβ : β.length = s := by simp [β, Nat.min_eq_left hs]
  have hγ : γ.length = e := by simp [γ, Nat.min_eq_left he]
  have hhead : I.HasHeadEvent u₀ t₀ := by
    refine ⟨s, Finset.mem_range.mpr ?_, e, Finset.mem_range.mpr ?_, ⟨?_, ?_⟩⟩
    · simp only [u₀, List.length_append, hβ]; omega
    · omega
    · refine ⟨by simp [u₀, hβ], by omega, ?_⟩
      simp [u₀, t₀, ← hβ, ← hγ]
    · have hss : s ≤ u₀.length := by simp [u₀, hβ]
      have hee : e ≤ t₀.length := by omega
      simpa only [hsplitu, hsplitt, LDFA.atCut_append _ _ _ hss,
        LDFA.atCut_append _ _ _ hee] using hd.2
  have hhole : I.IsHole (u₀ ++ θ) (t₀ ++ θ) := by rwa [← hsplitu, ← hsplitt]
  have hj₀ : I.J t₀ = some t₀.length := by
    rw [htl]
    exact I.J_of_append (hsplitt ▸ hj) (by omega)
  obtain ⟨hp, hc⟩ := I.preHole_of_completed_hole hhole hj₀ hhead
  refine ⟨u₀, t₀, θ, hsplitu, hsplitt, ?_, hp, hc⟩
  rw [hsplitt, List.drop_left]

/-- Safe reachability composes. -/
theorem safeReachable_trans {q r v : SA} (hqr : I.SafeReachable q r)
    (hrv : I.SafeReachable r v) : I.SafeReachable q v := by
  obtain ⟨u, hu, rfl⟩ := hqr
  obtain ⟨w, hw, rfl⟩ := hrv
  exact ⟨u ++ w, I.safeFrom_append.mpr ⟨hu, hw⟩, LDFA.runFrom_append _ _ _ _⟩

/-- Safety of a nonempty word separates its first transition and remaining run. -/
theorem safeFrom_cons {q : SA} {c : α} {w : Word α} :
    I.SafeFrom q (c :: w) ↔ q ∉ I.Bad ∧ I.SafeFrom (I.A.step q c) w := by
  rw [show c :: w = [c] ++ w from rfl, I.safeFrom_append]
  simp only [LDFA.runFrom, List.foldl_cons, List.foldl_nil]
  constructor
  · rintro ⟨h, hw⟩; exact ⟨I.safeFrom_start h, hw⟩
  · rintro ⟨hq, hw⟩
    refine ⟨?_, hw⟩
    intro i hi
    have hi' : i ≤ 1 := by simpa only [Finset.mem_range, List.length_singleton,
      Nat.lt_succ_iff] using hi
    interval_cases i
    · exact hq
    · exact I.safeFrom_start hw

/-- The state at the next cut is obtained by one transition. -/
theorem run_take_succ (q : SA) (w : Word α) {i : ℕ} (hi : i < w.length) :
    I.A.runFrom q (w.take (i + 1)) = I.A.step (I.A.runFrom q (w.take i)) w[i] := by
  rw [List.take_succ_eq_append_getElem hi, LDFA.runFrom_append]
  rfl

/-- A safe cycle is a finite viability certificate. -/
theorem cyclic_viable {q : SA} (hc : I.Cyclic q) : I.Viable q := by
  obtain ⟨w, hn, hw, he⟩ := hc
  have hp := List.length_pos_iff.mpr hn
  let f := fun i => I.A.runFrom q (w.take i)
  let T := (Finset.range w.length).image f
  refine ⟨T, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hi' := Finset.mem_range.mp hi
    refine ⟨(I.safeFrom_iff.mp hw) i (by omega), w[i], ?_⟩
    rw [← I.run_take_succ q w hi']
    by_cases hij : i + 1 < w.length
    · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hij, rfl⟩
    · have hlast : i + 1 = w.length := by omega
      simp only [hlast, List.take_length, he]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩

/-- Safe reachability of a viable state implies viability of the starting state. -/
theorem viable_of_reachable {q r : SA} (hr : I.SafeReachable q r) (hv : I.Viable r) :
    I.Viable q := by
  obtain ⟨w, hw, rfl⟩ := hr
  obtain ⟨ξ, hξ⟩ := (I.viable_iff _).mp hv
  exact (I.viable_iff _).mpr ⟨prepend w ξ, I.infiniteSafe_prepend hw hξ⟩

/-- Safe reachability preserves mortality. -/
theorem mortal_reachable {q r : SA} (hq : I.Mortal q) (hr : I.SafeReachable q r) :
    I.Mortal r := by
  refine ⟨?_, fun hv => hq.2 (I.viable_of_reachable hr hv)⟩
  obtain ⟨w, hw, rfl⟩ := hr
  exact I.safeFrom_end hw

/-- Every nonbad state is mortal, branching, or thin. -/
theorem state_kinds {q : SA} (hq : q ∉ I.Bad) :
    I.Mortal q ∨ I.Branching q ∨ I.Thin q := by
  classical
  by_cases hm : I.Mortal q
  · exact Or.inl hm
  · by_cases hb : I.Branching q
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨hq, hm, hb⟩)

/-- A factor of a safe path, with its endpoint equation. -/
theorem safe_segment {q : SA} {w : Word α} (hw : I.SafeFrom q w)
    {i j : ℕ} (hij : i ≤ j) (_hj : j ≤ w.length) :
    I.SafeFrom (I.A.runFrom q (w.take i)) ((w.drop i).take (j - i)) ∧
    I.A.runFrom (I.A.runFrom q (w.take i)) ((w.drop i).take (j - i)) =
      I.A.runFrom q (w.take j) := by
  have heq : w.take j = w.take i ++ (w.drop i).take (j - i) := by
    simpa [Nat.add_sub_of_le hij] using (List.take_add (l := w) (i := i) (j := j - i))
  have hs := I.safeFrom_prefix hw (List.take_prefix j w)
  rw [heq, I.safeFrom_append] at hs
  exact ⟨hs.2, by rw [← LDFA.runFrom_append, ← heq]⟩

/-- Equal states along a nonempty safe factor give a cycle. -/
theorem cyclic_of_repeat {q : SA} {w : Word α} (hw : I.SafeFrom q w)
    {i j : ℕ} (hij : i < j) (hj : j ≤ w.length)
    (he : I.A.runFrom q (w.take i) = I.A.runFrom q (w.take j)) :
    I.Cyclic (I.A.runFrom q (w.take i)) := by
  have hseg := I.safe_segment hw (by omega : i ≤ j) hj
  refine ⟨(w.drop i).take (j - i), ?_, hseg.1, hseg.2.trans he.symm⟩
  apply List.ne_nil_of_length_pos
  simp only [List.length_take, List.length_drop]
  omega

/-- The pigeonhole step shared by the mortal and thin arguments. -/
theorem path_repeat {q : SA} {w : Word α} (hl : Fintype.card SA ≤ w.length) :
    ∃ i j, i < j ∧ j ≤ w.length ∧
      I.A.runFrom q (w.take i) = I.A.runFrom q (w.take j) := by
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (w.length + 1) => I.A.runFrom q (w.take i)) (by simp; omega)
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with hh | hh
  · exact ⟨i, j, hh, by have := j.isLt; omega, he⟩
  · exact ⟨j, i, hh, by have := i.isLt; omega, he.symm⟩

/-- A reachable cyclic thin state has a unique safe letter. -/
theorem mortal_safe_word {q : SA} {w : Word α} (hq : I.Mortal q) (hw : I.SafeFrom q w) :
    w.length < Fintype.card SA ∧ I.Mortal (I.A.runFrom q w) := by
  refine ⟨?_, I.mortal_reachable hq ⟨w, hw, rfl⟩⟩
  by_contra hn
  obtain ⟨i, j, hij, hj, he⟩ := I.path_repeat (q := q) (by omega : Fintype.card SA ≤ w.length)
  have hc := I.cyclic_of_repeat hw hij hj he
  have hr : I.SafeReachable q (I.A.runFrom q (w.take i)) :=
    ⟨w.take i, I.safeFrom_prefix hw (List.take_prefix _ _), rfl⟩
  exact hq.2 (I.viable_of_reachable hr (I.cyclic_viable hc))

/-- Rotating a cycle past its first letter. -/
theorem cyclic_step {q : SA} {c : α} {v : Word α}
    (hw : I.SafeFrom q (c :: v)) (he : I.A.runFrom q (c :: v) = q) :
    I.Cyclic (I.A.step q c) := by
  have hs := I.safeFrom_cons.mp hw
  have hev : I.A.runFrom (I.A.step q c) v = q := he
  refine ⟨v ++ [c], by simp, I.safeFrom_append.mpr ⟨hs.2, ?_⟩, ?_⟩
  · rw [hev]
    exact I.safeFrom_prefix hw ⟨v, rfl⟩
  · rw [LDFA.runFrom_append, hev]; rfl

/-- The sole safe letter at a reachable cycle stays cyclic. -/
theorem thin_cyclic_letter {q r : SA} (hq : I.Thin q) (hr : I.SafeReachable q r)
    (hc : I.Cyclic r) : ∃ c, I.A.step r c ∉ I.Bad ∧ I.Cyclic (I.A.step r c) ∧
      ∀ d, I.A.step r d ∉ I.Bad → d = c := by
  obtain ⟨w, hn, hw, he⟩ := hc
  cases w with
  | nil => exact (hn rfl).elim
  | cons c v =>
    have hs := I.safeFrom_start (I.safeFrom_cons.mp hw).2
    refine ⟨c, hs, I.cyclic_step hw he, ?_⟩
    intro d hd
    by_contra hdc
    have hb : I.Branching q := by
      exact ⟨hq.1, r, hr, ⟨c :: v, by simp, hw, he⟩, c, d, Ne.symm hdc, hs, hd⟩
    exact hq.2.2 hb

/-- A safe path within a thin cyclic component stays cyclic. -/
theorem thin_cyclic_path {q r : SA} (hq : I.Thin q) (hr : I.SafeReachable q r)
    (hc : I.Cyclic r) {w : Word α} (hw : I.SafeFrom r w) :
    I.Cyclic (I.A.runFrom r w) := by
  induction w generalizing r with
  | nil => exact hc
  | cons c w ih =>
    have hs := I.safeFrom_cons.mp hw
    have hstep := I.safeFrom_start hs.2
    obtain ⟨d, _, hdcyc, hd⟩ := I.thin_cyclic_letter hq hr hc
    have hcd := hd c hstep
    have hc' : I.Cyclic (I.A.step r c) := hcd ▸ hdcyc
    apply ih (r := I.A.step r c) _ hc' hs.2
    exact I.safeReachable_trans hr ⟨[c], I.safeFrom_prefix hw ⟨w, rfl⟩, rfl⟩

/-- A safe path from a thin state to a mortal state is shorter than the state count. -/
theorem thin_mortal_endpoint_short {q : SA} {w : Word α} (hq : I.Thin q)
    (hw : I.SafeFrom q w) (hm : I.Mortal (I.A.runFrom q w)) :
    w.length < Fintype.card SA := by
  by_contra hn
  obtain ⟨i, j, hij, hj, he⟩ := I.path_repeat (q := q) (by omega : Fintype.card SA ≤ w.length)
  have hc := I.cyclic_of_repeat hw hij hj he
  have hr : I.SafeReachable q (I.A.runFrom q (w.take i)) :=
    ⟨w.take i, I.safeFrom_prefix hw (List.take_prefix _ _), rfl⟩
  have hsplit : I.SafeFrom q (w.take i ++ w.drop i) := by simpa using hw
  have hcyc := I.thin_cyclic_path hq hr hc (I.safeFrom_append.mp hsplit).2
  have hend : I.Cyclic (I.A.runFrom q w) := by
    simpa [← LDFA.runFrom_append] using hcyc
  exact hm.2 (I.cyclic_viable hend)

/-- A suffix of an infinitely safe run remains infinitely safe. -/
theorem infiniteSafe_shift {q : SA} {ξ : ℕ → α} (hξ : I.InfiniteSafe q ξ) (k : ℕ) :
    I.InfiniteSafe (I.A.streamRun q ξ k) (fun i => ξ (k + i)) := by
  intro n; simpa [streamRun_add] using hξ (k + n)

/-- All safe infinite runs from a reachable cyclic thin state have the same letters. -/
theorem thin_cyclic_unique {q r : SA} (hq : I.Thin q) (hr : I.SafeReachable q r)
    (hc : I.Cyclic r) {ξ η : ℕ → α} (hξ : I.InfiniteSafe r ξ) (hη : I.InfiniteSafe r η) :
    ξ = η := by
  have hstates (n : ℕ) : I.A.streamRun r ξ n = I.A.streamRun r η n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hp := I.infiniteSafe_prefix hξ n
      have hreach : I.SafeReachable q (I.A.streamRun r ξ n) := by
        rw [LDFA.streamRun_eq]
        exact I.safeReachable_trans hr ⟨streamPrefix ξ n, hp, rfl⟩
      have hcyc : I.Cyclic (I.A.streamRun r ξ n) := by
        rw [LDFA.streamRun_eq]; exact I.thin_cyclic_path hq hr hc hp
      obtain ⟨c, _, _, hu⟩ := I.thin_cyclic_letter hq hreach hcyc
      have h₁ := hu (ξ n) (hξ (n + 1))
      have h₂ := hu (η n) (by simpa [LDFA.streamRun, ← ih] using hη (n + 1))
      simp only [LDFA.streamRun, ih, h₁, h₂]
  funext n
  have hp := I.infiniteSafe_prefix hξ n
  have hreach : I.SafeReachable q (I.A.streamRun r ξ n) := by
    rw [LDFA.streamRun_eq]
    exact I.safeReachable_trans hr ⟨streamPrefix ξ n, hp, rfl⟩
  have hcyc : I.Cyclic (I.A.streamRun r ξ n) := by
    rw [LDFA.streamRun_eq]; exact I.thin_cyclic_path hq hr hc hp
  obtain ⟨c, _, _, hu⟩ := I.thin_cyclic_letter hq hreach hcyc
  exact (hu (ξ n) (hξ (n + 1))).trans
    (hu (η n) (by simpa [LDFA.streamRun, hstates n] using hη (n + 1))).symm

end FinitePaths

/-- A bounded lasso presentation, including the safe path and return equation. -/
def Lasso (q : SA) (ξ : ℕ → α) : Prop := ∃ α₀ l : Word α,
  l ≠ [] ∧ α₀.length + l.length ≤ Fintype.card SA ∧
  I.SafeFrom q (α₀ ++ l) ∧ I.A.runFrom q (α₀ ++ l) = I.A.runFrom q α₀ ∧
  ξ = prepend α₀ (periodicStream l)

/-- Every safe stream from a thin state has a bounded lasso representation. -/
theorem thin_lasso {q : SA} (hq : I.Thin q) {ξ : ℕ → α} (hξ : I.InfiniteSafe q ξ) :
    I.Lasso q ξ := by
  let N := Fintype.card SA
  let w := streamPrefix ξ N
  have hw : I.SafeFrom q w := I.infiniteSafe_prefix hξ N
  obtain ⟨i, j, hij, hj, he⟩ := I.path_repeat (q := q) (w := w) (by simp [w, N])
  have hiN : i ≤ N := by simp only [w, streamPrefix_length] at hj; omega
  have hjN : j ≤ N := by simpa [w] using hj
  have htake (k : ℕ) (hk : k ≤ N) : w.take k = streamPrefix ξ k := by
    simpa only [w] using streamPrefix_take ξ hk
  have hs : I.A.streamRun q ξ i = I.A.streamRun q ξ j := by
    simpa [htake i hiN, htake j hjN, ← LDFA.streamRun_eq] using he
  have hc : I.Cyclic (I.A.streamRun q ξ i) := by
    simpa [htake i hiN, ← LDFA.streamRun_eq] using I.cyclic_of_repeat hw hij hj he
  have hr : I.SafeReachable q (I.A.streamRun q ξ i) := by
    rw [LDFA.streamRun_eq]
    exact ⟨streamPrefix ξ i, I.infiniteSafe_prefix hξ i, rfl⟩
  have ht : (fun k => ξ (i + k)) = (fun k => ξ (j + k)) :=
    I.thin_cyclic_unique hq hr hc (I.infiniteSafe_shift hξ i)
      (hs ▸ I.infiniteSafe_shift hξ j)
  have hper : StreamPeriod (fun k => ξ (i + k)) (j - i) := by
    intro k
    have hh := congrFun ht k
    change ξ (i + (k + (j - i))) = ξ (i + k)
    rw [show i + (k + (j - i)) = j + k by omega]
    exact hh.symm
  let α₀ := streamPrefix ξ i
  let l := streamPrefix (fun k => ξ (i + k)) (j - i)
  have hl : l ≠ [] := by
    apply List.ne_nil_of_length_pos; simp [l]; omega
  have hal : α₀ ++ l = streamPrefix ξ j := by
    rw [← streamPrefix_add]; congr 1; omega
  refine ⟨α₀, l, hl, by simp [α₀, l]; omega, ?_, ?_, ?_⟩
  · rw [hal]; exact I.infiniteSafe_prefix hξ j
  · simpa [hal, α₀, ← LDFA.streamRun_eq] using hs.symm
  · have htail : (fun k => ξ (i + k)) = periodicStream l :=
      streamPeriod_eq_periodicStream (by omega) hper
    funext k
    by_cases hk : k < i
    · simp [prepend, α₀, hk, streamPrefix]
    · have hh := congrFun htail (k - i)
      simpa [prepend, α₀, show ¬ k < i from hk, Nat.add_sub_of_le (by omega : i ≤ k)] using hh

/-- Repeating a nonempty safe cycle gives an infinitely safe stream. -/
theorem cycle_infiniteSafe {q : SA} {w : Word α} (hn : w ≠ [])
    (hw : I.SafeFrom q w) (he : I.A.runFrom q w = q) :
    I.InfiniteSafe q (periodicStream w) := by
  have hp := List.length_pos_iff.mpr hn
  have hprefix : IsStreamPrefix w (periodicStream w) := by
    rw [IsStreamPrefix, ← periodicStream_fixed hn, prepend_prefix]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hl : n ≤ w.length
    · rw [LDFA.streamRun_eq, prepend_streamPrefix hprefix hl]
      exact (I.safeFrom_iff.mp hw) n hl
    · have hlt : n - w.length < n := by omega
      have hle : w.length ≤ n := by omega
      have hr := LDFA.streamRun_prepend I.A q w (periodicStream w) (n - w.length)
      rw [periodicStream_fixed hn, Nat.add_sub_of_le hle, he] at hr
      rw [hr]
      exact ih _ hlt

/-- A lasso represents an infinitely safe stream. -/
theorem lasso_safe {q : SA} {ξ : ℕ → α} (h : I.Lasso q ξ) : I.InfiniteSafe q ξ := by
  obtain ⟨α₀, l, hn, _, hw, he, rfl⟩ := h
  have hs := I.safeFrom_append.mp hw
  rw [LDFA.runFrom_append] at he
  exact I.infiniteSafe_prepend hs.1 (I.cycle_infiniteSafe hn hs.2 he)

/-- Safe streams at a thin state are exactly its bounded lassos. -/
theorem thin_lasso_iff {q : SA} (hq : I.Thin q) (ξ : ℕ → α) :
    I.InfiniteSafe q ξ ↔ I.Lasso q ξ := ⟨I.thin_lasso hq, I.lasso_safe⟩

omit [Inhabited α] in
/-- A comparison survives exactly when every finite prefix keeps it. -/
theorem survives_iff_keeps {u t : Word α} {s e : ℕ} (hc : Cross u t s e) (ξ : ℕ → α) :
    Survives u t s e ξ ↔ ∀ n, Keeps u t s e (streamPrefix ξ n) := by
  constructor
  · intro h n
    have hext : Cross (u ++ streamPrefix ξ n) (t ++ streamPrefix ξ n) s e :=
      ⟨by have := hc.1; simp; omega, by have := hc.2.1; simp; omega, h n⟩
    exact ((cross_append_iff hc.2.1).mp hext).2
  · intro h n
    exact ((cross_append_iff hc.2.1).mpr ⟨hc, h n⟩).2.2

omit [Inhabited α] in
/-- An aligned comparison survives every stream. -/
theorem aligned_survives {u t : Word α} {s e : ℕ} (ha : Aligned u t s e) (ξ : ℕ → α) :
    Survives u t s e ξ := by
  have hc : Cross u t s e := ⟨ha.1, ha.2.1, ha.2.2 ▸ List.prefix_rfl⟩
  exact (survives_iff_keeps hc ξ).mpr (fun n => aligned_keeps ha _)

/-- A nonaligned comparison survives exactly its periodic overhang stream. -/
theorem survives_iff_periodic {u t : Word α} {s e : ℕ} (hc : Cross u t s e)
    (hn : ¬ Aligned u t s e) (ξ : ℕ → α) :
    Survives u t s e ξ ↔ ξ = periodicStream (overhang u t s e) := by
  have ho : overhang u t s e ≠ [] := fun h => hn ((cross_aligned_iff hc).mpr h)
  rw [survives_iff_keeps hc]
  constructor
  · intro h
    funext i
    have hp := (periodic_prefix_iff ho).mp (h (i + 1))
    have hh := streamPrefix_iff.mp hp i (by simp)
    simpa only [streamPrefix, List.getElem_ofFn] using hh
  · rintro rfl n
    exact (periodic_prefix_iff ho).mpr (streamPrefix_self _ n)

omit [Inhabited α] in
/-- A finite safe prefix breaking all events gives a survivor-free stream. -/
theorem completes_survivorFree {u t w : Word α} {ξ : ℕ → α}
    (hc : I.Completes u t w) (hp : IsStreamPrefix w ξ) : I.SurvivorFree u t ξ := by
  intro s e he hs
  have hk := (survives_iff_keeps he.1 ξ).mp hs w.length
  rw [hp] at hk
  exact hc.2 s e he hk

omit [Inhabited α] in
/-- Finitely many events have a common breaking prefix. -/
theorem survivorFree_completes {u t : Word α} {ξ : ℕ → α}
    (hs : I.InfiniteSafe (I.A.run u) ξ) (hf : I.SurvivorFree u t ξ) :
    ∃ n, I.Completes u t (streamPrefix ξ n) := by
  classical
  let P := Fin (u.length + 1) × Fin (t.length + 1)
  have hb (p : P) : ∃ n, I.Event u t p.1 p.2 → ¬ Keeps u t p.1 p.2 (streamPrefix ξ n) := by
    by_cases he : I.Event u t p.1 p.2
    · have hn : ¬ ∀ n, Keeps u t p.1 p.2 (streamPrefix ξ n) := by
        intro h; exact hf _ _ he ((survives_iff_keeps he.1 ξ).mpr h)
      obtain ⟨n, hn⟩ := not_forall.mp hn
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (he h).elim⟩
  choose n hn using hb
  let N := Finset.univ.sup n
  refine ⟨N, I.infiniteSafe_prefix hs N, ?_⟩
  intro s e he hk
  let p : P := (⟨s, by have := he.1.1; omega⟩, ⟨e, by have := he.1.2.1; omega⟩)
  have hle : n p ≤ N := Finset.le_sup (f := n) (Finset.mem_univ p)
  exact hn p he (keeps_prefix hk (streamPrefix_prefix ξ hle))

omit [Inhabited α] in
/-- Delete the stretch between equal states of a safe path. -/
theorem erase_loop {q : SA} {w : Word α} (hw : I.SafeFrom q w) {i j : ℕ}
    (hij : i < j) (hj : j ≤ w.length)
    (he : I.A.runFrom q (w.take i) = I.A.runFrom q (w.take j)) :
    I.SafeFrom q (w.take i ++ w.drop j) ∧
    I.A.runFrom q (w.take i ++ w.drop j) = I.A.runFrom q w ∧
    (w.take i ++ w.drop j).length < w.length := by
  have hs : I.SafeFrom q (w.take j ++ w.drop j) := by simpa using hw
  have ht := (I.safeFrom_append.mp hs).2
  refine ⟨I.safeFrom_append.mpr ⟨I.safeFrom_prefix hw (List.take_prefix _ _), he ▸ ht⟩, ?_, ?_⟩
  · rw [LDFA.runFrom_append, he, ← LDFA.runFrom_append, List.take_append_drop]
  · simp only [List.length_append, List.length_take, List.length_drop]; omega

omit [Inhabited α] in
/-- Safe reachability has a witness shorter than the number of states. -/
theorem short_safeReachable {q r : SA} (hr : I.SafeReachable q r) :
    ∃ w, I.SafeFrom q w ∧ I.A.runFrom q w = r ∧ w.length < Fintype.card SA := by
  classical
  have hex : ∃ n, ∃ w : Word α, I.SafeFrom q w ∧ I.A.runFrom q w = r ∧ w.length = n := by
    obtain ⟨w, hw, he⟩ := hr; exact ⟨w.length, w, hw, he, rfl⟩
  obtain ⟨w, hw, he, hl⟩ := Nat.find_spec hex
  refine ⟨w, hw, he, ?_⟩
  by_contra hn
  obtain ⟨i, j, hij, hj, hijstate⟩ := I.path_repeat (q := q) (by omega : Fintype.card SA ≤ w.length)
  obtain ⟨hv, hev, hlen⟩ := I.erase_loop hw hij hj hijstate
  have hmin := Nat.find_min' hex ⟨w.take i ++ w.drop j, hv, hev.trans he, rfl⟩
  omega

omit [Inhabited α] in
/-- A cyclic state has a nonempty safe cycle bounded by the state count. -/
theorem short_cyclic {q : SA} (hc : I.Cyclic q) :
    ∃ w, w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q ∧ w.length ≤ Fintype.card SA := by
  classical
  have hex : ∃ n, ∃ w : Word α, w ≠ [] ∧ I.SafeFrom q w ∧ I.A.runFrom q w = q ∧ w.length = n := by
    obtain ⟨w, hn, hw, he⟩ := hc; exact ⟨w.length, w, hn, hw, he, rfl⟩
  obtain ⟨w, hn, hw, he, hl⟩ := Nat.find_spec hex
  refine ⟨w, hn, hw, he, ?_⟩
  by_contra hlarge
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin w.length => I.A.runFrom q (w.take i)) (by simp; omega)
  have hpair : ∃ i j, i < j ∧ j < w.length ∧
      I.A.runFrom q (w.take i) = I.A.runFrom q (w.take j) := by
    rcases lt_or_gt_of_ne (show a.val ≠ b.val from fun h => hab (Fin.ext h)) with h | h
    · exact ⟨a, b, h, b.isLt, heq⟩
    · exact ⟨b, a, h, a.isLt, heq.symm⟩
  obtain ⟨i, j, hij, hj, hijstate⟩ := hpair
  obtain ⟨hv, hev, hlen⟩ := I.erase_loop hw hij (by omega) hijstate
  have hvn : w.take i ++ w.drop j ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have hmin := Nat.find_min' hex ⟨w.take i ++ w.drop j, hvn, hv, hev.trans he, rfl⟩
  omega

/-- Repeated complete traversals of a cycle return to its starting state. -/
theorem cycle_streamRun_mul {q : SA} {w : Word α} (hn : w ≠ [])
    (he : I.A.runFrom q w = q) (k : ℕ) :
    I.A.streamRun q (periodicStream w) (k * w.length) = q := by
  induction k with
  | zero => simp [LDFA.streamRun]
  | succ k ih =>
    have hh := LDFA.streamRun_prepend I.A q w (periodicStream w) (k * w.length)
    rw [periodicStream_fixed hn, he] at hh
    simpa [Nat.succ_mul, Nat.add_comm, ih] using hh

end TwoWordInstance

end DeciENSSE.Core.Words
