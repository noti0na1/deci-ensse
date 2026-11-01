import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import DeciENSSE.Core.Words.Transport

/-! # Structure of non-mortal holes

Safe paths split into mortal, branching, and thin cases. Periodic streams and
bounded lassos characterize the thin case and give the three-case decomposition.

## Main declarations

- `SS2.hole_decomposition`
- `SS2.thin_lasso_iff`
- `SS2.breaker`
- `threeCases`
-/

namespace DeciENSSE.Core

variable {α : Type*}

/-- A stream prefix has its prescribed length. -/
@[simp] theorem length_streamPrefix (ξ : ℕ → α) (n : ℕ) :
    (streamPrefix ξ n).length = n := by simp [streamPrefix]

/-- Indexing a stream prefix recovers the corresponding stream letter. -/
@[simp] theorem getElem_streamPrefix (ξ : ℕ → α) (n i : ℕ) (h : i < n) :
    (streamPrefix ξ n)[i]'(by simpa using h) = ξ i := by simp [streamPrefix]

/-- Taking a shorter stream prefix gives the prefix of that length. -/
@[simp] theorem take_streamPrefix (ξ : ℕ → α) (n k : ℕ) :
    (streamPrefix ξ n).take k = streamPrefix ξ (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [streamPrefix]

/-- A shorter stream prefix is a list prefix of a longer one. -/
theorem streamPrefix_prefix (ξ : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    (streamPrefix ξ m).IsPrefix (streamPrefix ξ n) := by
  rw [List.prefix_iff_eq_take]
  simp [h]

/-- Prefixing an infinite word by a finite word. -/
def prepend (w : Word α) (ξ : ℕ → α) (i : ℕ) : α :=
  if h : i < w.length then w[i] else ξ (i - w.length)

/-- Prepending the empty word leaves a stream unchanged. -/
@[simp] theorem prepend_nil (ξ : ℕ → α) : prepend [] ξ = ξ := by
  funext i; simp [prepend]

/-- The prepended word is a prefix of the resulting stream. -/
theorem prepend_prefix (w : Word α) (ξ : ℕ → α) :
    streamPrefix (prepend w ξ) w.length = w := by
  apply List.ext_getElem <;> simp [streamPrefix, prepend]

/-- A prefix beyond the prepended word splits into word and stream prefixes. -/
theorem prepend_prefix_add (w : Word α) (ξ : ℕ → α) (n : ℕ) :
    streamPrefix (prepend w ξ) (w.length + n) = w ++ streamPrefix ξ n := by
  induction n with
  | zero => simpa only [Nat.add_zero, show streamPrefix ξ 0 = [] from rfl,
      List.append_nil] using prepend_prefix w ξ
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih]
    simp [prepend, List.append_assoc, streamPrefix_succ]

/-- Prepending concatenated words agrees with successive prepending. -/
theorem prepend_assoc (u v : Word α) (ξ : ℕ → α) :
    prepend (u ++ v) ξ = prepend u (prepend v ξ) := by
  funext i
  by_cases hi : i < u.length
  · simp [prepend, hi, show i < u.length + v.length by omega,
      List.getElem_append_left]
  · by_cases hj : i < u.length + v.length
    · simp [prepend, hi, hj, show i - u.length < v.length by omega,
        List.getElem_append_right (by omega : u.length ≤ i)]
    · simp [prepend, hi, hj, show ¬ i - u.length < v.length by omega,
        Nat.sub_sub]

/-- Prepending a fixed finite word is injective on streams. -/
theorem prepend_injective (w : Word α) : Function.Injective (prepend w) := by
  intro ξ η h
  funext n
  have := congrFun h (w.length + n)
  simpa [prepend] using this

namespace LDFA
variable {S : Type*} (M : LDFA α S)

/-- A cut within the first word is unaffected by appending a suffix. -/
theorem atCut_append (u v : Word α) {s : ℕ} (h : s ≤ u.length) :
    M.atCut (u ++ v) s = M.atCut u s := by
  simp [atCut, List.take_append_of_le_length h]

/-- Running across a prepended word continues from its endpoint. -/
theorem streamRun_prepend (q : S) (w : Word α) (ξ : ℕ → α) (n : ℕ) :
    M.streamRun q (prepend w ξ) (w.length + n) =
      M.streamRun (M.runFrom q w) ξ n := by
  simp only [streamRun_eq, prepend_prefix_add, runFrom_append]

end LDFA

/-- A finite word is a prefix of an infinite word. -/
def StreamPrefix (w : Word α) (ξ : ℕ → α) : Prop := streamPrefix ξ w.length = w

/-- Stream-prefix membership is pointwise agreement on the finite word. -/
theorem streamPrefix_iff {w : Word α} {ξ : ℕ → α} :
    StreamPrefix w ξ ↔ ∀ i (hi : i < w.length), w[i] = ξ i := by
  constructor
  · intro h i hi
    have := congrArg (fun v => v[i]?) h
    simpa [streamPrefix, hi] using this.symm
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simpa [streamPrefix] using (h i hj).symm

/-- Each finite stream prefix is a prefix of that stream. -/
theorem streamPrefix_self (ξ : ℕ → α) (n : ℕ) : StreamPrefix (streamPrefix ξ n) ξ := by
  simp [StreamPrefix]

/-- A list prefix of a stream prefix is again a stream prefix. -/
theorem streamPrefix_mono {u v : Word α} {ξ : ℕ → α}
    (h : StreamPrefix v ξ) (hp : u.IsPrefix v) : StreamPrefix u ξ := by
  change streamPrefix ξ u.length = u
  calc
    streamPrefix ξ u.length = (streamPrefix ξ v.length).take u.length := by
      simp [hp.length_le]
    _ = v.take u.length := by rw [h]
    _ = u := (List.prefix_iff_eq_take.mp hp).symm

/-- Two prefixes of a stream are ordered by their lengths. -/
theorem streamPrefix_compare {u v : Word α} {ξ : ℕ → α}
    (hu : StreamPrefix u ξ) (hv : StreamPrefix v ξ) (hl : u.length ≤ v.length) :
    u.IsPrefix v := by
  rw [← hu, ← hv]
  exact streamPrefix_prefix ξ hl

variable [Inhabited α]

/-- Repetition; the value on the empty period is irrelevant to all uses. -/
def periodicStream (w : Word α) (i : ℕ) : α := w[i % w.length]?.getD default

/-- A letter within the period is recovered by the periodic stream. -/
theorem periodicStream_get {w : Word α} (hw : w ≠ []) (i : ℕ) :
    periodicStream w i = w[i % w.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr hw)) := by
  simp [periodicStream, List.getElem?_eq_getElem (Nat.mod_lt i (List.length_pos_iff.mpr hw))]

/-- Finite periodic prefixes are exactly the prefixes fixed by prepending a period. -/
theorem periodic_prefix_iff {o θ : Word α} (ho : o ≠ []) :
    θ.IsPrefix (o ++ θ) ↔ StreamPrefix θ (periodicStream o) := by
  have hop := List.length_pos_iff.mpr ho
  rw [streamPrefix_iff]
  constructor
  · intro h i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have heq := h.getElem hi
      by_cases hio : i < o.length
      · simpa [periodicStream_get ho, Nat.mod_eq_of_lt hio,
          List.getElem_append_left hio] using heq
      · have hle : o.length ≤ i := by omega
        have hj : i - o.length < θ.length := by omega
        have hmod : (i - o.length) % o.length = i % o.length :=
          (Nat.mod_eq_sub_mod hle).symm
        rw [List.getElem_append_right hle] at heq
        rw [heq, ih (i - o.length) (by omega) hj]
        simp [periodicStream, hmod]
  · intro h
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simp, ?_⟩
    intro i hi
    rw [h i hi]
    by_cases hio : i < o.length
    · simp [List.getElem_append_left hio, periodicStream_get ho, Nat.mod_eq_of_lt hio]
    · have hle : o.length ≤ i := by omega
      rw [List.getElem_append_right hle, h (i - o.length) (by omega)]
      simp [periodicStream, ← Nat.mod_eq_sub_mod hle]

/-- Infinite periods are stated with the later index on the left. -/
def StreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop := ∀ i, ξ (i + p) = ξ i

/-- The length of a nonempty period word is a stream period. -/
theorem periodicStream_period (w : Word α) : StreamPeriod (periodicStream w) w.length := by
  intro i; simp [periodicStream]

omit [Inhabited α] in
/-- A periodic stream depends only on the index modulo its period. -/
theorem streamPeriod_mod {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    ξ n = ξ (n % p) := by
  by_cases hp : p = 0
  · simp [hp]
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < p
      · simp [Nat.mod_eq_of_lt hn]
      · have hle : p ≤ n := by omega
        calc
          ξ n = ξ (n - p) := by simpa [Nat.sub_add_cancel hle] using h (n - p)
          _ = ξ ((n - p) % p) := ih _ (by omega)
          _ = ξ (n % p) := by rw [← Nat.mod_eq_sub_mod hle]

omit [Inhabited α] in
/-- Finite prefixes of a periodic stream have the corresponding word period. -/
theorem streamPeriod_prefix {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    List.HasPeriod (streamPrefix ξ n) p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hi' : i < n := by simpa only [length_streamPrefix] using (by omega : i < (streamPrefix ξ
    n).length)
  have hip : i + p < n := by simp only [length_streamPrefix] at hi; omega
  simp only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi', dite_eq_left hip, h i]

omit [Inhabited α] in
/-- Fine–Wilf for finite words. -/
theorem fine_wilf {w : Word α} {p q : ℕ} (hp : w.HasPeriod p) (hq : w.HasPeriod q)
    (hl : p + q - Nat.gcd p q ≤ w.length) : w.HasPeriod (Nat.gcd p q) := hp.gcd hq hl

omit [Inhabited α] in
/-- The greatest common divisor of two periods is a period. -/
theorem streamPeriod_gcd {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by
  intro i
  let n := i + p + q + Nat.gcd p q + 1
  have hg := fine_wilf (streamPeriod_prefix hp n) (streamPeriod_prefix hq n) (by simp [n]; omega)
  have hh := (List.hasPeriod_iff_getElem?.mp hg) i (by simp [n]; omega)
  have hi : i < n := by dsimp [n]; omega
  have hj : i + Nat.gcd p q < n := by dsimp [n]; omega
  simpa only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi, dite_eq_left hj,
    Option.some.injEq] using hh.symm

/-- Prepending one period leaves its periodic stream unchanged. -/
theorem periodicStream_fixed {o : Word α} (ho : o ≠ []) :
    prepend o (periodicStream o) = periodicStream o := by
  funext i
  by_cases hi : i < o.length
  · simp [prepend, hi, periodicStream_get ho, Nat.mod_eq_of_lt hi]
  · simp [prepend, hi, periodicStream, ← Nat.mod_eq_sub_mod (by omega : o.length ≤ i)]

/-- Infinite self-overlap characterizes periodic streams. -/
theorem prepend_fixed_iff {o : Word α} {ξ : ℕ → α} (ho : o ≠ []) :
    prepend o ξ = ξ ↔ ξ = periodicStream o := by
  constructor
  · intro h
    have hper : StreamPeriod ξ o.length := by
      intro i
      have hh := congrFun h (i + o.length)
      simpa [prepend, Nat.add_sub_cancel_right] using hh.symm
    funext i
    rw [streamPeriod_mod hper i, periodicStream_get ho]
    have hi := Nat.mod_lt i (List.length_pos_iff.mpr ho)
    have hh := congrFun h (i % o.length)
    simpa [prepend, hi] using hh.symm
  · rintro rfl; exact periodicStream_fixed ho

omit [Inhabited α] in
/-- Taking a prefix at a known stream prefix recovers the finite word. -/
theorem prepend_streamPrefix {w : Word α} {ξ : ℕ → α} {n : ℕ}
    (h : StreamPrefix w ξ) (hn : n ≤ w.length) :
    streamPrefix ξ n = w.take n := by
  rw [← h, take_streamPrefix]
  simp [hn]


omit [Inhabited α] in
/-- A stream prefix splits at any intermediate length. -/
theorem streamPrefix_add (ξ : ℕ → α) (k n : ℕ) :
    streamPrefix ξ (k + n) = streamPrefix ξ k ++ streamPrefix (fun i => ξ (k + i)) n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih, streamPrefix_succ, List.append_assoc]

omit [Inhabited α] in
/-- Running a stream splits at an intermediate time. -/
theorem streamRun_add {S : Type*} (M : LDFA α S) (q : S) (ξ : ℕ → α) (k n : ℕ) :
    M.streamRun q ξ (k + n) = M.streamRun (M.streamRun q ξ k) (fun i => ξ (k + i)) n := by
  simp [LDFA.streamRun_eq, streamPrefix_add, LDFA.runFrom_append]

omit [Inhabited α] in
/-- Shifting a periodic stream preserves its period. -/
theorem streamPeriod_shift {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (k : ℕ) :
    StreamPeriod (fun i => ξ (k + i)) p := by
  intro i; simpa [Nat.add_assoc] using h (k + i)

/-- A positive stream period determines a finite periodic representation. -/
theorem streamPeriod_eq_periodicStream {ξ : ℕ → α} {p : ℕ}
    (hp : 0 < p) (h : StreamPeriod ξ p) : ξ = periodicStream (streamPrefix ξ p) := by
  funext i
  rw [streamPeriod_mod h i]
  simp [periodicStream, streamPrefix, Nat.mod_lt i hp]

omit [Inhabited α] in
/-- Two periodic infinite words are determined by their Fine–Wilf window. -/
theorem periodic_agreement {ξ η : ℕ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hξ : StreamPeriod ξ p) (hη : StreamPeriod η q)
    (he : ∀ i < p + q - 1, ξ i = η i) : ξ = η := by
  let L := p + q - 1
  let w := streamPrefix ξ L
  have hLp : p ≤ L := by dsimp [L]; omega
  have hLq : q ≤ L := by dsimp [L]; omega
  have hw : w = streamPrefix η L := by
    apply List.ext_getElem
    · simp [w]
    · intro i hi hj
      simpa [w, streamPrefix] using he i (by simpa using hj)
  have hgpos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp
  have hgw : w.HasPeriod (Nat.gcd p q) := by
    apply fine_wilf (streamPeriod_prefix hξ L)
      (show w.HasPeriod q by rw [hw]; exact streamPeriod_prefix hη L)
    simp only [length_streamPrefix]
    dsimp [L]; omega
  have hξg (i : ℕ) : ξ i = ξ (i % Nat.gcd p q) := by
    have hip := Nat.mod_lt i hp
    have hil : i % p < L := by omega
    have hmod : (i % p) % Nat.gcd p q = i % Nat.gcd p q :=
      Nat.mod_mod_of_dvd i (Nat.gcd_dvd_left p q)
    have hh := hgw.getElem?_mod (Nat.gcd p q) (i % p) w (by simpa [w] using hil)
    have hsmall : (i % p) % Nat.gcd p q < L := lt_of_le_of_lt (Nat.mod_le _ _) hil
    have hh' : ξ ((i % p) % Nat.gcd p q) = ξ (i % p) := by
      simpa only [w, streamPrefix, List.getElem?_ofFn, dite_eq_left hsmall,
        dite_eq_left hil, Option.some.injEq] using hh
    rw [streamPeriod_mod hξ i, ← hh', hmod]
  have hηg (i : ℕ) : η i = η (i % Nat.gcd p q) := by
    have hiq := Nat.mod_lt i hq
    have hil : i % q < L := by omega
    have hmod : (i % q) % Nat.gcd p q = i % Nat.gcd p q :=
      Nat.mod_mod_of_dvd i (Nat.gcd_dvd_right p q)
    have hh := hgw.getElem?_mod (Nat.gcd p q) (i % q) w (by simpa [w] using hil)
    rw [hw] at hh
    have hsmall : (i % q) % Nat.gcd p q < L := lt_of_le_of_lt (Nat.mod_le _ _) hil
    have hh' : η ((i % q) % Nat.gcd p q) = η (i % q) := by
      simpa only [streamPrefix, List.getElem?_ofFn, dite_eq_left hsmall,
        dite_eq_left hil, Option.some.injEq] using hh
    rw [streamPeriod_mod hη i, ← hh', hmod]
  funext i
  rw [hξg, hηg]
  apply he
  have hg := Nat.gcd_le_left q hp
  have hi := Nat.mod_lt i hgpos
  dsimp [L] at hLp
  omega

omit [Inhabited α] in
/-- Eventual periods and a finite window of agreement determine a stream. -/
theorem ultimately_periodic_agreement {ξ η : ℕ → α} {a b p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hξ : StreamPeriod (fun i => ξ (a + i)) p)
    (hη : StreamPeriod (fun i => η (b + i)) q)
    (he : ∀ i < max a b + p + q - 1, ξ i = η i) : ξ = η := by
  let k := max a b
  have hx : StreamPeriod (fun i => ξ (k + i)) p := by
    have hh := streamPeriod_shift hξ (k - a)
    simpa only [← Nat.add_assoc, Nat.add_sub_of_le (show a ≤ k from le_max_left a b)] using hh
  have hy : StreamPeriod (fun i => η (k + i)) q := by
    have hh := streamPeriod_shift hη (k - b)
    simpa only [← Nat.add_assoc, Nat.add_sub_of_le (show b ≤ k from le_max_right a b)] using hh
  have ht := periodic_agreement hp hq hx hy (fun i hi => he (k + i) (by dsimp [k]; omega))
  funext i
  by_cases hi : i < k
  · exact he i (by dsimp [k] at hi; omega)
  · have hh := congrFun ht (i - k)
    simpa [Nat.add_sub_of_le (by omega : k ≤ i)] using hh


/-- Fine–Wilf forces the next letter after a sufficiently long periodic stretch. -/
theorem periodic_departure_breaks {o l : Word α} (ho : o ≠ []) (hl : l ≠ [])
    (α₀ : Word α) (n : ℕ) (hlen : o.length + l.length - 1 ≤ n)
    (b : α) (hb : b ≠ periodicStream l n) :
    ¬ StreamPrefix (α₀ ++ streamPrefix (periodicStream l) n ++ [b])
      (periodicStream o) := by
  intro h
  let η := prepend α₀ (periodicStream l)
  let v := α₀ ++ streamPrefix (periodicStream l) n
  have hv : StreamPrefix v (periodicStream o) :=
    streamPrefix_mono h (List.prefix_append v _)
  have hvη : StreamPrefix v η := by
    simp only [StreamPrefix, v, List.length_append, length_streamPrefix, η, prepend_prefix_add]
  have hηper : StreamPeriod (fun i => η (α₀.length + i)) l.length := by
    simpa [η, prepend] using periodicStream_period l
  have he : periodicStream o = η := by
    apply ultimately_periodic_agreement (a := 0) (b := α₀.length)
      (List.length_pos_iff.mpr ho) (List.length_pos_iff.mpr hl)
      (by simpa using periodicStream_period o) hηper
    intro i hi
    have hiv : i < v.length := by simp only [v, List.length_append, length_streamPrefix]; omega
    exact (streamPrefix_iff.mp hv i hiv).symm.trans (streamPrefix_iff.mp hvη i hiv)
  have hh := streamPrefix_iff.mp h v.length (by simp [v])
  change (v ++ [b])[v.length] = periodicStream o v.length at hh
  simp only [List.getElem_append_right (le_refl v.length), Nat.sub_self,
    List.getElem_cons_zero] at hh
  rw [he] at hh
  have hvalue : η v.length = periodicStream l n := by simp [η, v, prepend]
  exact hb (hh.trans hvalue)


namespace SS2
variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

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
  simpa [take_streamPrefix, Nat.min_eq_left (by simpa using hs),
    ← LDFA.streamRun_eq] using h s

/-- A safe finite word may be prepended to an infinitely safe continuation. -/
theorem infiniteSafe_prepend {q : SA} {w : Word α} {ξ : ℕ → α}
    (hw : I.SafeFrom q w) (hξ : I.InfiniteSafe (I.A.runFrom q w) ξ) :
    I.InfiniteSafe q (prepend w ξ) := by
  intro n
  by_cases hn : n ≤ w.length
  · have ht : streamPrefix (prepend w ξ) n = w.take n := by
      have := take_streamPrefix (prepend w ξ) w.length n
      simpa [prepend_prefix, Nat.min_eq_left hn] using this.symm
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

/-- A completing continuation, def:prehole. -/
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

/-- FH puts every head cut before the first rejection. -/
theorem head_cut_le_J {u t : Word α} {s e j : ℕ} (hf : I.FH)
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
theorem hole_decomposition {u t : Word α} (hf : I.FH) (hh : I.IsHole u t) :
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

/-- Every nonbad state safely reaches itself. -/
theorem safeReachable_refl {q : SA} (hq : q ∉ I.Bad) : I.SafeReachable q q :=
  ⟨[], by simpa [SafeFrom] using hq, rfl⟩

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

/-- A branching state is not mortal. -/
theorem branching_not_mortal {q : SA} (hq : I.Branching q) : ¬ I.Mortal q := by
  rintro ⟨_, hm⟩
  obtain ⟨r, hr, hc, _⟩ := hq.2
  exact hm (I.viable_of_reachable hr (I.cyclic_viable hc))

/-- Every nonbad state is mortal, branching, or thin. -/
theorem state_kinds {q : SA} (hq : q ∉ I.Bad) :
    I.Mortal q ∨ I.Branching q ∨ I.Thin q := by
  classical
  by_cases hm : I.Mortal q
  · exact Or.inl hm
  · by_cases hb : I.Branching q
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨hq, hm, hb⟩)

/-- Safe reachability of a branching state implies branching. -/
theorem branching_of_reachable {q r : SA} (hr : I.SafeReachable q r)
    (hb : I.Branching r) : I.Branching q := by
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw, _⟩ := hr; exact I.safeFrom_start hw
  · obtain ⟨v, hv, hc, hletters⟩ := hb.2
    exact ⟨v, I.safeReachable_trans hr hv, hc, hletters⟩

/-- A safely reachable nonmortal state from a thin state is thin. -/
theorem thin_reachable {q r : SA} (hq : I.Thin q) (hr : I.SafeReachable q r) :
    I.Mortal r ∨ I.Thin r := by
  have hs : r ∉ I.Bad := by obtain ⟨w, hw, rfl⟩ := hr; exact I.safeFrom_end hw
  rcases I.state_kinds hs with hm | hb | ht
  · exact Or.inl hm
  · exact (hq.2.2 (I.branching_of_reachable hr hb)).elim
  · exact Or.inr ht

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
  have hiN : i ≤ N := by simp only [w, length_streamPrefix] at hj; omega
  have hjN : j ≤ N := by simpa [w] using hj
  have htake (k : ℕ) (hk : k ≤ N) : w.take k = streamPrefix ξ k := by simp [w, hk]
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
  have hprefix : StreamPrefix w (periodicStream w) := by
    rw [StreamPrefix, ← periodicStream_fixed hn, prepend_prefix]
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

/-- A thin state has a bounded safe lasso. -/
theorem thin_lasso_exists {q : SA} (hq : I.Thin q) : ∃ ξ, I.Lasso q ξ := by
  have hv : I.Viable q := by
    by_contra hn; exact hq.2.1 ⟨hq.1, hn⟩
  obtain ⟨ξ, hξ⟩ := (I.viable_iff q).mp hv
  exact ⟨ξ, I.thin_lasso hq hξ⟩

/-- A safe word with no lasso extension has a mortal endpoint and bounded length. -/
theorem thin_no_lasso_prefix {q : SA} (hq : I.Thin q) {w : Word α} (hw : I.SafeFrom q w)
    (hn : ¬ ∃ ξ, I.Lasso q ξ ∧ StreamPrefix w ξ) :
    I.Mortal (I.A.runFrom q w) ∧ w.length < Fintype.card SA := by
  have hm : I.Mortal (I.A.runFrom q w) := by
    refine ⟨I.safeFrom_end hw, ?_⟩
    intro hv
    obtain ⟨ξ, hξ⟩ := (I.viable_iff _).mp hv
    exact hn ⟨prepend w ξ, I.thin_lasso hq (I.infiniteSafe_prepend hw hξ), prepend_prefix w ξ⟩
  exact ⟨hm, I.thin_mortal_endpoint_short hq hw hm⟩


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
    (hc : I.Completes u t w) (hp : StreamPrefix w ξ) : I.SurvivorFree u t ξ := by
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
/-- A safe survivor-free continuation completes a pre-hole to a hole. -/
theorem hasHole_of_survivorFree {u t : Word α} (hp : I.IsPreHole u t) {ξ : ℕ → α}
    (hs : I.InfiniteSafe (I.A.run u) ξ) (hf : I.SurvivorFree u t ξ) : I.HasHole := by
  obtain ⟨n, hn⟩ := I.survivorFree_completes hs hf
  exact ⟨u ++ streamPrefix ξ n, t ++ streamPrefix ξ n, I.preHole_complete hp hn⟩

/-- The thin survivor-free case is equivalent to its bounded lasso formulation. -/
theorem thin_survivorFree_iff {u t : Word α} (hq : I.Thin (I.A.run u)) :
    (∃ ξ, I.InfiniteSafe (I.A.run u) ξ ∧ I.SurvivorFree u t ξ) ↔
    ∃ ξ, I.Lasso (I.A.run u) ξ ∧ I.SurvivorFree u t ξ := by
  simp only [I.thin_lasso_iff hq]


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

omit [Inhabited α] in
/-- The hole-to-cases direction; FH is used only by the pre-hole decomposition. -/
theorem cases_of_hole (hf : I.FH) (hh : I.HasHole) : I.NonMortalCase ∨ I.HasMortalHole := by
  classical
  obtain ⟨u, t, hh⟩ := hh
  obtain ⟨u₀, t₀, θ, hu, ht, _, hp, hc⟩ := I.hole_decomposition hf hh
  have hq : I.A.run u₀ ∉ I.Bad := I.safeFrom_end hp.1
  have hj : I.J t = some t₀.length := by rw [ht]; exact I.J_append hp.2.1 θ
  have htail : t.length - t₀.length = θ.length := by simp [ht]
  have hend : I.A.run u = I.A.runFrom (I.A.run u₀) θ := by
    simp [hu, LDFA.run, LDFA.runFrom_append]
  have mortalCase (hm : I.Mortal (I.A.run u)) (hl : θ.length < Fintype.card SA) :
      I.HasMortalHole := ⟨u, t, hh, hm, t₀.length, by simp [hj], by simpa [htail] using hl⟩
  rcases I.state_kinds hq with hm | hb | hthin
  · have hs := I.mortal_safe_word hm hc.1
    exact Or.inr (mortalCase (hend ▸ hs.2) hs.1)
  · exact Or.inl ⟨u₀, t₀, hp, Or.inl hb⟩
  · by_cases hv : I.Viable (I.A.run u)
    · obtain ⟨ξ, hξ⟩ := (I.viable_iff _).mp hv
      have hsafe := I.infiniteSafe_prepend hc.1 (hend ▸ hξ)
      exact Or.inl ⟨u₀, t₀, hp, Or.inr ⟨hthin, prepend θ ξ, hsafe,
        I.completes_survivorFree hc (prepend_prefix θ ξ)⟩⟩
    · have hm : I.Mortal (I.A.run u) := ⟨I.safeFrom_end hh.1, hv⟩
      exact Or.inr (mortalCase hm (I.thin_mortal_endpoint_short hthin hc.1 (hend ▸ hm)))


/-- A branching state has a bounded safe continuation breaking all nonaligned comparisons. -/
theorem breaker {u t : Word α} (hb : I.Branching (I.A.run u)) :
    ∃ θ, I.SafeFrom (I.A.run u) θ ∧ θ.length ≤ u.length + 3 * Fintype.card SA ∧
      ∀ s e, Cross u t s e → ¬ Aligned u t s e → ¬ Keeps u t s e θ := by
  classical
  obtain ⟨r, hr, hcyc, a, b, hab, ha, hb'⟩ := hb.2
  obtain ⟨α₀, hα, hαr, hαlen⟩ := I.short_safeReachable hr
  obtain ⟨l, hln, hl, hlr, hllen⟩ := I.short_cyclic hcyc
  have hlpos := List.length_pos_iff.mpr hln
  let k := u.length / l.length + 2
  let n := k * l.length
  have hnlo : u.length + l.length ≤ n := by
    have hm := Nat.mod_lt u.length hlpos
    have hd := Nat.mod_add_div u.length l.length
    dsimp [n, k]
    rw [Nat.add_mul, Nat.mul_comm (u.length / l.length) l.length]
    omega
  have hnhi : n ≤ u.length + 2 * l.length := by
    have hd := Nat.mod_add_div u.length l.length
    dsimp [n, k]
    rw [Nat.add_mul, Nat.mul_comm (u.length / l.length) l.length]
    omega
  let c := if a = periodicStream l n then b else a
  have hcne : c ≠ periodicStream l n := by
    dsimp [c]
    split_ifs with h
    · exact fun he => hab (h.trans he.symm)
    · exact h
  have hcsafe : I.A.step r c ∉ I.Bad := by
    dsimp [c]
    split_ifs <;> assumption
  let θ := α₀ ++ streamPrefix (periodicStream l) n ++ [c]
  have hs := I.cycle_infiniteSafe hln hl hlr
  have hrun : I.A.runFrom r (streamPrefix (periodicStream l) n) = r := by
    rw [← LDFA.streamRun_eq]; exact I.cycle_streamRun_mul hln hlr k
  refine ⟨θ, ?_, ?_, ?_⟩
  · apply I.safeFrom_append.mpr
    refine ⟨I.safeFrom_append.mpr ⟨hα, ?_⟩, ?_⟩
    · rw [hαr]; exact I.infiniteSafe_prefix hs n
    · rw [LDFA.runFrom_append, hαr, hrun]
      apply I.safeFrom_cons.mpr
      refine ⟨I.safeFrom_start hl, ?_⟩
      simpa [SafeFrom] using hcsafe
  · simp only [θ, List.length_append, length_streamPrefix, List.length_singleton]
    omega
  · intro s e hc ha hk
    have ho : overhang u t s e ≠ [] := fun hh => ha ((cross_aligned_iff hc).mpr hh)
    apply periodic_departure_breaks ho hln α₀ n ?_ c hcne ((periodic_prefix_iff ho).mp hk)
    have hh := cross_offset_le hc
    rw [overhang_length]
    omega

/-- A branching pre-hole has a bounded completing continuation. -/
theorem preHole_breaker {u t : Word α} (hp : I.IsPreHole u t)
    (hb : I.Branching (I.A.run u)) :
    ∃ θ, I.Completes u t θ ∧ θ.length ≤ u.length + 3 * Fintype.card SA := by
  obtain ⟨θ, hs, hl, hbreak⟩ := I.breaker (t := t) hb
  refine ⟨θ, ⟨hs, ?_⟩, hl⟩
  intro s e he
  apply hbreak s e he.1
  intro ha
  exact hp.2.2.2 s (Finset.mem_range.mpr (by have := he.1.1; omega))
    e (Finset.mem_range.mpr (by have := he.1.2.1; omega)) ⟨he, ha⟩

/-- Holes split into non-mortal and mortal cases over arbitrary finite state types. -/
theorem three_cases (hf : I.FH) : I.HasHole ↔ I.NonMortalCase ∨ I.HasMortalHole := by
  constructor
  · exact I.cases_of_hole hf
  · rintro (⟨u, t, hp, hb | ⟨_, ξ, hs, hfree⟩⟩ | ⟨u, t, hm⟩)
    · obtain ⟨θ, hθ, _⟩ := I.preHole_breaker hp hb
      exact ⟨u ++ θ, t ++ θ, I.preHole_complete hp hθ⟩
    · exact I.hasHole_of_survivorFree hp hs hfree
    · exact ⟨u, t, hm.1⟩


end SS2

/-- The three-case decomposition holds over every finite alphabet. -/
theorem threeCases [Fintype α] [DecidableEq α] : ThreeCases α := by
  intro a b c d I hf
  exact I.three_cases hf

namespace NonMortalExamples

open CoreExamples

/-- The breaker applies when zero is unsafe and one and two are safe. -/
theorem ternary_breaker :
    ∃ θ : Word (Fin 3), ternaryBranch.SafeFrom 0 θ ∧ θ.length ≤ 7 ∧
      ∀ s e, SS2.Cross ([1] : Word (Fin 3)) [] s e →
        ¬ SS2.Aligned ([1] : Word (Fin 3)) [] s e →
        ¬ SS2.Keeps ([1] : Word (Fin 3)) [] s e θ := by
  simpa only [show ternaryBranch.A.run [1] = 0 from rfl,
    List.length_singleton, Fintype.card_fin] using
    ternaryBranch.breaker (u := [1]) (t := [])
      (show ternaryBranch.Branching (ternaryBranch.A.run [1]) from ternary_branching)

/-- A concrete safe breaker: follow the one-cycle three times, then take two. -/
theorem ternary_breaker_word :
    ternaryBranch.SafeFrom 0 [1, 1, 1, 2] ∧
      ([1, 1, 1, 2] : Word (Fin 3)).length ≤ 7 ∧
      ∀ s e, SS2.Cross ([1] : Word (Fin 3)) [] s e →
        ¬ SS2.Aligned ([1] : Word (Fin 3)) [] s e →
        ¬ SS2.Keeps ([1] : Word (Fin 3)) [] s e [1, 1, 1, 2] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro s e hc ha
  have hs : s ≤ 1 := hc.1
  have he : e = 0 := by have := hc.2.1; simp only [List.length_nil] at this; omega
  subst e
  interval_cases s
  · unfold SS2.Keeps SS2.overhang
    decide +kernel
  · exact (ha (by unfold SS2.Aligned; decide +kernel)).elim

/-- This regression has a genuine non-aligned cross comparison to break. -/
theorem ternary_cross :
    SS2.Cross ([1] : Word (Fin 3)) [] 0 0 ∧
      ¬ SS2.Aligned ([1] : Word (Fin 3)) [] 0 0 := by
  unfold SS2.Cross SS2.Aligned
  decide +kernel

/-- Exercise the departure theorem itself with a third-alphabet letter. -/
theorem ternary_departure :
    ¬ StreamPrefix ([1, 1, 1, 2] : Word (Fin 3)) (periodicStream [1]) := by
  exact periodic_departure_breaks (o := [1]) (l := [1])
    (by decide +kernel) (by decide +kernel) [] 3 (by decide +kernel)
    2 (by decide +kernel)

end NonMortalExamples


end DeciENSSE.Core
