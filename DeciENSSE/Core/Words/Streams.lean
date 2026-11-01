import Mathlib.Data.List.PeriodicityLemma
import DeciENSSE.Core.Words.LDFA

/-! # Infinite words and periodic agreement

Finite prefixes, prepending, and periods describe infinite words. Agreement on a long
finite prefix determines periodic streams and bounds how long a departure can stay hidden.
Stream prefixes and their basic lemmas come from `DeciNSSE.RejectedTail`.

## Main declarations

- `prepend`, `IsStreamPrefix`: finite prefixes of infinite words.
- `periodicStream`, `StreamPeriod`: periodic infinite words.
- `periodic_agreement`, `ultimately_periodic_agreement`: finite agreement criteria.
- `periodic_departure_breaks`: a departure breaks a periodic comparison.
-/

namespace DeciENSSE.Core.Words
open DeciNSSE.RejectedTail

variable {α : Type*}

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
def IsStreamPrefix (w : Word α) (ξ : ℕ → α) : Prop := streamPrefix ξ w.length = w

/-- Stream-prefix membership is pointwise agreement on the finite word. -/
theorem streamPrefix_iff {w : Word α} {ξ : ℕ → α} :
    IsStreamPrefix w ξ ↔ ∀ i (hi : i < w.length), w[i] = ξ i := by
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
theorem streamPrefix_self (ξ : ℕ → α) (n : ℕ) : IsStreamPrefix (streamPrefix ξ n) ξ := by
  simp [IsStreamPrefix]

/-- A list prefix of a stream prefix is again a stream prefix. -/
theorem streamPrefix_mono {u v : Word α} {ξ : ℕ → α}
    (h : IsStreamPrefix v ξ) (hp : u.IsPrefix v) : IsStreamPrefix u ξ := by
  change streamPrefix ξ u.length = u
  calc
    streamPrefix ξ u.length = (streamPrefix ξ v.length).take u.length := by
      exact (streamPrefix_take ξ hp.length_le).symm
    _ = v.take u.length := by rw [h]
    _ = u := (List.prefix_iff_eq_take.mp hp).symm

/-- Two prefixes of a stream are ordered by their lengths. -/
theorem streamPrefix_compare {u v : Word α} {ξ : ℕ → α}
    (hu : IsStreamPrefix u ξ) (hv : IsStreamPrefix v ξ) (hl : u.length ≤ v.length) :
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
    θ.IsPrefix (o ++ θ) ↔ IsStreamPrefix θ (periodicStream o) := by
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
  have hi' : i < n := by simpa only [streamPrefix_length] using (by omega : i < (streamPrefix ξ
    n).length)
  have hip : i + p < n := by simp only [streamPrefix_length] at hi; omega
  simp only [streamPrefix, List.getElem?_ofFn, dite_eq_left hi', dite_eq_left hip, h i]

omit [Inhabited α] in
/-- The greatest common divisor of two periods is a period. -/
theorem streamPeriod_gcd {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by
  intro i
  let n := i + p + q + Nat.gcd p q + 1
  have hg := (streamPeriod_prefix hp n).gcd (streamPeriod_prefix hq n)
    (by simp [n]; omega)
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
    (h : IsStreamPrefix w ξ) (hn : n ≤ w.length) :
    streamPrefix ξ n = w.take n := by
  exact (streamPrefix_take ξ hn).symm.trans (congrArg (List.take n) h)

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
    apply List.HasPeriod.gcd (streamPeriod_prefix hξ L)
      (show w.HasPeriod q by rw [hw]; exact streamPeriod_prefix hη L)
    simp only [streamPrefix_length]
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
    ¬ IsStreamPrefix (α₀ ++ streamPrefix (periodicStream l) n ++ [b])
      (periodicStream o) := by
  intro h
  let η := prepend α₀ (periodicStream l)
  let v := α₀ ++ streamPrefix (periodicStream l) n
  have hv : IsStreamPrefix v (periodicStream o) :=
    streamPrefix_mono h (List.prefix_append v _)
  have hvη : IsStreamPrefix v η := by
    simp only [IsStreamPrefix, v, List.length_append, streamPrefix_length, η, prepend_prefix_add]
  have hηper : StreamPeriod (fun i => η (α₀.length + i)) l.length := by
    simpa [η, prepend] using periodicStream_period l
  have he : periodicStream o = η := by
    apply ultimately_periodic_agreement (a := 0) (b := α₀.length)
      (List.length_pos_iff.mpr ho) (List.length_pos_iff.mpr hl)
      (by simpa using periodicStream_period o) hηper
    intro i hi
    have hiv : i < v.length := by simp only [v, List.length_append, streamPrefix_length]; omega
    exact (streamPrefix_iff.mp hv i hiv).symm.trans (streamPrefix_iff.mp hvη i hiv)
  have hh := streamPrefix_iff.mp h v.length (by simp [v])
  change (v ++ [b])[v.length] = periodicStream o v.length at hh
  simp only [List.getElem_append_right (le_refl v.length), Nat.sub_self,
    List.getElem_cons_zero] at hh
  rw [he] at hh
  have hvalue : η v.length = periodicStream l n := by simp [η, v, prepend]
  exact hb (hh.trans hvalue)

end DeciENSSE.Core.Words
