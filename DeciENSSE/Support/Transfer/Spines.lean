import DeciNSSE.Constraints.Closure


/-! # Path pins as fresh constraint chains

Four kinds of spine chains encode presence or absence of extreme labels.
A shared bottom or top filler supplies every child outside the chosen path.

## Main declarations

- `ConstraintN.lift`
- `Spines.extend`
- `noBotChainN`
- `botChainN`
- `topChainN`
- `noTopChainN`
-/

namespace DeciENSSE.Support
open DeciNSSE

variable {n k m : ℕ}

/-! ## Lifting constraints -/

/-- Reindex a constraint along `Fin.castAdd m`. -/
def ConstraintN.lift (ϕ : Constraint n k) (m : ℕ) : Constraint n (k + m) :=
  ϕ.map (Lit.rename (Fin.castAdd m))

/-! ## Spine nodes and chain literals -/

/-- The children of a spine node: `next` at the spine letter `i`, and the shared
filler `fill` at each of the other `n - 1` positions. -/
def spineChildren (i : Fin n) (next fill : V k) : Fin n → V k :=
  fun j => if j = i then next else fill

/-- The selected child is the next spine variable. -/
@[simp] theorem spineChildren_self (i : Fin n) (next fill : V k) :
    spineChildren i next fill i = next := by simp [spineChildren]


/-- Every child is either the next spine variable or the filler. -/
theorem spineChildren_eq_or (i j : Fin n) (next fill : V k) :
    spineChildren i next fill j = next ∨ spineChildren i next fill j = fill := by
  by_cases h : j = i <;> simp [spineChildren, h]

/-- A lower link `f(…, next at i, …, b, …) ≤ a`. -/
def lowerLinkN (i : Fin n) (a next b : V k) : Lit n k :=
  .fLe (spineChildren i next b) a

/-- An upper link `a ≤ f(…, next at i, …, t, …)`. -/
def upperLinkN (i : Fin n) (a next t : V k) : Lit n k :=
  .leF a (spineChildren i next t)

/-- Encode the lower constructor links along a path. -/
def lowerStepsN (v : ℕ → V k) (b : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => lowerLinkN i (v 0) (v 1) b :: lowerStepsN (fun j => v (j + 1)) b ν

/-- Encode the upper constructor links along a path. -/
def upperStepsN (v : ℕ → V k) (t : V k) : List (Fin n) → Constraint n k
  | [] => []
  | i :: ν => upperLinkN i (v 0) (v 1) t :: upperStepsN (fun j => v (j + 1)) t ν

/-- Exact membership in a lower chain: position `j` reads the letter `ν[j]`. -/
theorem mem_lowerStepsN_iff {v : ℕ → V k} {b : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ lowerStepsN v b ν ↔
      ∃ j, ∃ hj : j < ν.length, l = lowerLinkN ν[j] (v j) (v (j + 1)) b := by
  induction ν generalizing v with
  | nil => simp [lowerStepsN]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

/-- Upper-chain literals are exactly the links at positions along the path. -/
theorem mem_upperStepsN_iff {v : ℕ → V k} {t : V k} {ν : List (Fin n)} {l : Lit n k} :
    l ∈ upperStepsN v t ν ↔
      ∃ j, ∃ hj : j < ν.length, l = upperLinkN ν[j] (v j) (v (j + 1)) t := by
  induction ν generalizing v with
  | nil => simp [upperStepsN]
  | cons i ν ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

/-- A lower chain contains no upper constructor literal. -/
theorem leF_not_mem_lowerStepsN (v : ℕ → V k) (b c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.leF c a ∉ lowerStepsN v b ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_lowerStepsN_iff.mp h
  simp [lowerLinkN] at he


/-- An upper chain contains no lower constructor literal. -/
theorem fLe_not_mem_upperStepsN (v : ℕ → V k) (t c : V k) (a : Fin n → V k)
    (ν : List (Fin n)) : Lit.fLe a c ∉ upperStepsN v t ν := by
  intro h
  obtain ⟨_, _, he⟩ := mem_upperStepsN_iff.mp h
  simp [upperLinkN] at he


namespace Spines

open Safety

/-! ## Chain semantics -/

/-- A lower link compares its designated spine children with the parent. -/
theorem holds_lowerLinkN (ρ : V k → DeciNSSE.Tree n) (i : Fin n) (a next b : V k) :
    Covariant.holds ρ (lowerLinkN i a next b) ↔
      DeciNSSE.Tree.node (ρ ∘ spineChildren i next b) ≤ ρ a := Iff.rfl

/-- An upper link compares its parent with the designated spine children. -/
theorem holds_upperLinkN (ρ : V k → DeciNSSE.Tree n) (i : Fin n) (a next t : V k) :
    Covariant.holds ρ (upperLinkN i a next t) ↔
      ρ a ≤ DeciNSSE.Tree.node (ρ ∘ spineChildren i next t) := Iff.rfl

/-- A lower chain propagates its endpoint below the followed tree. -/
theorem lowerStepsN_bound (ρ : V k → DeciNSSE.Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (lowerStepsN v b ν)) :
    ρ (v ν.length) ≤ trace (ρ (v 0)) ν := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (Covariant.sat_cons _ _ _).mp h
    have hedge : ρ (v 1) ≤ descend (ρ (v 0)) i := by
      simpa using descend_mono he i
    exact le_trans (ih _ hr) (trace_mono hedge ν)

/-- An upper chain bounds the trace by its endpoint. -/
theorem upperStepsN_bound (ρ : V k → DeciNSSE.Tree n) (v : ℕ → V k) (t : V k)
    (ν : List (Fin n)) (h : Covariant.Sat ρ (upperStepsN v t ν)) :
    trace (ρ (v 0)) ν ≤ ρ (v ν.length) := by
  induction ν generalizing v with
  | nil => exact le_rfl
  | cons i ν ih =>
    obtain ⟨he, hr⟩ := (Covariant.sat_cons _ _ _).mp h
    have hedge : descend (ρ (v 0)) i ≤ ρ (v 1) := by
      simpa using descend_mono he i
    exact le_trans (trace_mono hedge ν) (ih _ hr)

/-- The constructor with bottom children lies below exactly the nonbottom trees. -/
theorem node_bot_le_iff (t : DeciNSSE.Tree n) :
    DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.bot) ≤ t ↔ t ≠ DeciNSSE.Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp only [DeciNSSE.Tree.le_bot_iff, DeciNSSE.Tree.node_ne_bot, ne_eq, not_true_eq_false]
  · simp
  · simp

/-- Exactly the nontop trees lie below the constructor with top children. -/
theorem le_node_top_iff (t : DeciNSSE.Tree n) :
    t ≤ DeciNSSE.Tree.node (fun _ => DeciNSSE.Tree.top) ↔ t ≠ DeciNSSE.Tree.top := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp only [DeciNSSE.Tree.top_le_iff, DeciNSSE.Tree.node_ne_top, ne_eq, not_true_eq_false]
  · simp

/-- The canonical assignment follows actual subtrees and freezes at a leaf. -/
theorem lowerStepsN_sat (ρ : V k → DeciNSSE.Tree n) (v : ℕ → V k) (b : V k)
    (ν : List (Fin n)) (t : DeciNSSE.Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (hb : ρ b = DeciNSSE.Tree.bot) (ht : trace t ν ≠ DeciNSSE.Tree.bot) :
    Covariant.Sat ρ (lowerStepsN v b ν) := by
  induction ν generalizing v t with
  | nil => simp [lowerStepsN, Covariant.Sat]
  | cons i ν ih =>
    have hroot : t ≠ DeciNSSE.Tree.bot := by rintro rfl; simp at ht
    apply (Covariant.sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_lowerLinkN, h0]
      rcases t.eq_bot_or_eq_top_or_node with h | rfl | ⟨a, rfl⟩
      · exact False.elim (hroot h)
      · exact DeciNSSE.Tree.le_top _
      · rw [DeciNSSE.Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, hb]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

/-- Following actual traces satisfies an upper chain with a top filler. -/
theorem upperStepsN_sat (ρ : V k → DeciNSSE.Tree n) (v : ℕ → V k) (tv : V k)
    (ν : List (Fin n)) (t : DeciNSSE.Tree n)
    (hv : ∀ j, j ≤ ν.length → ρ (v j) = trace t (ν.take j))
    (htv : ρ tv = DeciNSSE.Tree.top) (ht : trace t ν ≠ DeciNSSE.Tree.top) :
    Covariant.Sat ρ (upperStepsN v tv ν) := by
  induction ν generalizing v t with
  | nil => simp [upperStepsN, Covariant.Sat]
  | cons i ν ih =>
    have hroot : t ≠ DeciNSSE.Tree.top := by rintro rfl; simp at ht
    apply (Covariant.sat_cons _ _ _).mpr
    constructor
    · have h0 := hv 0 (by simp)
      have h1 := hv 1 (by simp)
      simp only [List.take_zero, trace_nil] at h0
      simp only [List.take_succ_cons, List.take_zero, trace_cons, trace_nil] at h1
      rw [holds_upperLinkN, h0]
      rcases t.eq_bot_or_eq_top_or_node with rfl | h | ⟨a, rfl⟩
      · exact DeciNSSE.Tree.bot_le _
      · exact False.elim (hroot h)
      · rw [DeciNSSE.Tree.node_le_node_iff]
        intro j
        by_cases hj : j = i
        · subst hj; simp [h1]
        · simp [spineChildren, hj, htv]
    · apply ih _ (descend t i) _ ht
      intro j hj
      simpa [List.take_succ_cons] using hv (j + 1) (by simp; omega)

/-! ## Fresh variables and simultaneous extensions -/

/-- The old variables keep their indices. With `L` the spine length, lower
chain positions `1..L` are `k + j - 1`, upper chain positions are
`k + L + j - 1`, the bottom filler is `k + 2L` and the top filler `k + 2L + 1`. -/
def xv (x : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + j - 1, by omega⟩ else Fin.castAdd _ x

/-- The upper-chain variable at a position, with the old variable at position zero. -/
def yv (y : V k) (L j : ℕ) : V (k + (2 * L + 2)) :=
  if h : 0 < j ∧ j ≤ L then ⟨k + L + j - 1, by omega⟩ else Fin.castAdd _ y

/-- The shared bottom filler after the two fresh chains. -/
def bv (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L, by omega⟩
/-- The shared top filler after the two fresh chains. -/
def tv (k L : ℕ) : V (k + (2 * L + 2)) := ⟨k + 2 * L + 1, by omega⟩

/-- Position zero of the lower chain is the embedded old variable. -/
@[simp] theorem xv_zero (x : V k) (L : ℕ) : xv x L 0 = Fin.castAdd _ x := by
  simp [xv]
/-- Position zero of the upper chain is the embedded old variable. -/
@[simp] theorem yv_zero (y : V k) (L : ℕ) : yv y L 0 = Fin.castAdd _ y := by
  simp [yv]


/-- One extension fills both chains at once; their fresh blocks cannot interfere. -/
def extend (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (z : V (k + (2 * ν.length + 2))) : DeciNSSE.Tree n :=
  if h : z.val < k then ρ ⟨z.val, h⟩
  else if z.val < k + ν.length then trace (ρ x) (ν.take (z.val - k + 1))
  else if z.val < k + 2 * ν.length then
    trace (ρ y) (ν.take (z.val - (k + ν.length) + 1))
  else if z.val = k + 2 * ν.length then DeciNSSE.Tree.bot else DeciNSSE.Tree.top

/-- The canonical extension preserves each old value. -/
@[simp] theorem extend_old (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (z : V k) : extend ρ x y ν (Fin.castAdd _ z) = ρ z := by
  simp [extend, z.isLt]

/-- Restricting the canonical extension recovers the original assignment. -/
theorem extend_restrict (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν ∘ Fin.castAdd _ = ρ := by
  funext z; simp

/-- The canonical extension assigns bottom to the bottom filler. -/
@[simp] theorem extend_bv (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (bv k ν.length) = DeciNSSE.Tree.bot := by
  simp [extend, bv, show ¬ k + 2 * ν.length < k by omega,
    show ¬ k + 2 * ν.length < k + ν.length by omega]

/-- The canonical extension assigns top to the top filler. -/
@[simp] theorem extend_tv (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n)) :
    extend ρ x y ν (tv k ν.length) = DeciNSSE.Tree.top := by
  simp [extend, tv, show ¬ k + 2 * ν.length + 1 < k by omega,
    show ¬ k + 2 * ν.length + 1 < k + ν.length by omega,
    show ¬ k + 2 * ν.length + 1 < k + 2 * ν.length by omega]

/-- The lower chain follows the original tree along path prefixes. -/
theorem extend_xv (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (xv x ν.length j) = trace (ρ x) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + j - 1 < k := by omega
    have hlt : k + j - 1 < k + ν.length := by omega
    have he : k + j - 1 - k + 1 = j := by omega
    simp [xv, hp, extend, hge, hlt, he]

/-- The upper chain follows the original tree along path prefixes. -/
theorem extend_yv (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (j : ℕ) (hj : j ≤ ν.length) :
    extend ρ x y ν (yv y ν.length j) = trace (ρ y) (ν.take j) := by
  by_cases hz : j = 0
  · subst j; simp
  · have hp : 0 < j ∧ j ≤ ν.length := ⟨by omega, hj⟩
    have hge : ¬ k + ν.length + j - 1 < k := by omega
    have hge' : ¬ k + ν.length + j - 1 < k + ν.length := by omega
    have hlt : k + ν.length + j - 1 < k + 2 * ν.length := by omega
    have he : k + ν.length + j - 1 - (k + ν.length) + 1 = j := by omega
    simp [yv, hp, extend, hge, hge', hlt, he]

end Spines

open Safety Spines

/-! ## The four chain encodings -/

/-- `x` has no bottom at any prefix of `ν`: a lower chain ending in `f(⊥,…,⊥)`. -/
def noBotChainN (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerStepsN (xv x ν.length) (bv k ν.length) ν ++
    [.fLe (fun _ => bv k ν.length) (xv x ν.length ν.length), .eqBot (bv k ν.length)]

/-- `y` has a bottom at some prefix of `ν`: an upper chain ending in `⊥`. -/
def botChainN (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperStepsN (yv y ν.length) (tv k ν.length) ν ++
    [.eqBot (yv y ν.length ν.length), .eqTop (tv k ν.length)]

/-- `x` has a top at some prefix of `ν`: a lower chain ending in `⊤`. -/
def topChainN (x : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  lowerStepsN (xv x ν.length) (bv k ν.length) ν ++
    [.eqTop (xv x ν.length ν.length), .eqBot (bv k ν.length)]

/-- `y` has no top at any prefix of `ν`: an upper chain ending in `f(⊤,…,⊤)`. -/
def noTopChainN (y : V k) (ν : List (Fin n)) : Constraint n (k + (2 * ν.length + 2)) :=
  upperStepsN (yv y ν.length) (tv k ν.length) ν ++
    [.leF (yv y ν.length ν.length) (fun _ => tv k ν.length), .eqTop (tv k ν.length)]

namespace Spines

variable {ν : List (Fin n)} {x y : V k} {ρ' : V (k + (2 * ν.length + 2)) → DeciNSSE.Tree n}

/-- A solution of the chain encoding gives a nonbottom trace. -/
theorem noBotChainN_sound (h : Covariant.Sat ρ' (noBotChainN x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν ≠ DeciNSSE.Tree.bot := by
  obtain ⟨hs, he⟩ := (Covariant.sat_append _ _ _).mp h
  have he' : DeciNSSE.Tree.node (fun _ => ρ' (bv k ν.length)) ≤ ρ' (xv x ν.length ν.length) ∧
      ρ' (bv k ν.length) = DeciNSSE.Tree.bot := by
    simpa [Covariant.Sat, Covariant.holds, Function.comp_def] using he
  have hb := lowerStepsN_bound _ _ _ _ hs
  rw [xv_zero] at hb
  apply (node_bot_le_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact le_trans h1 hb

/-- A solution of the chain encoding gives a bottom trace. -/
theorem botChainN_sound (h : Covariant.Sat ρ' (botChainN y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν = DeciNSSE.Tree.bot := by
  obtain ⟨hs, he⟩ := (Covariant.sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) = DeciNSSE.Tree.bot ∧
      ρ' (tv k ν.length) = DeciNSSE.Tree.top := by simpa [Covariant.Sat, Covariant.holds] using he
  have hb := upperStepsN_bound _ _ _ _ hs
  rw [yv_zero, he'.1] at hb
  exact (DeciNSSE.Tree.le_bot_iff _).mp hb

/-- A solution of the chain encoding gives a top trace. -/
theorem topChainN_sound (h : Covariant.Sat ρ' (topChainN x ν)) :
    trace (ρ' (Fin.castAdd _ x)) ν = DeciNSSE.Tree.top := by
  obtain ⟨hs, he⟩ := (Covariant.sat_append _ _ _).mp h
  have he' : ρ' (xv x ν.length ν.length) = DeciNSSE.Tree.top ∧
      ρ' (bv k ν.length) = DeciNSSE.Tree.bot := by simpa [Covariant.Sat, Covariant.holds] using he
  have hb := lowerStepsN_bound _ _ _ _ hs
  rw [xv_zero, he'.1] at hb
  exact (DeciNSSE.Tree.top_le_iff _).mp hb

/-- A solution of the chain encoding gives a nontop trace. -/
theorem noTopChainN_sound (h : Covariant.Sat ρ' (noTopChainN y ν)) :
    trace (ρ' (Fin.castAdd _ y)) ν ≠ DeciNSSE.Tree.top := by
  obtain ⟨hs, he⟩ := (Covariant.sat_append _ _ _).mp h
  have he' : ρ' (yv y ν.length ν.length) ≤ DeciNSSE.Tree.node (fun _ => ρ' (tv k ν.length)) ∧
      ρ' (tv k ν.length) = DeciNSSE.Tree.top := by simpa [Covariant.Sat, Covariant.holds,
        Function.comp_def] using he
  have hb := upperStepsN_bound _ _ _ _ hs
  rw [yv_zero] at hb
  apply (le_node_top_iff _).mp
  have h1 := he'.1
  rw [he'.2] at h1
  exact le_trans hb h1

/-- An assignment with a nonbottom trace extends to solve the chain encoding. -/
theorem noBotChainN_extend (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν ≠ DeciNSSE.Tree.bot) : Covariant.Sat (extend ρ x y ν) (noBotChainN x ν) := by
  apply (Covariant.sat_append _ _ _).mpr
  constructor
  · exact lowerStepsN_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..) h
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.holds, he, Function.comp_def, node_bot_le_iff] using h

/-- An assignment with a bottom trace extends to solve the chain encoding. -/
theorem botChainN_extend (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν = DeciNSSE.Tree.bot) : Covariant.Sat (extend ρ x y ν) (botChainN y ν) := by
  apply (Covariant.sat_append _ _ _).mpr
  constructor
  · exact upperStepsN_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..)
      (by rw [h]; exact DeciNSSE.Tree.bot_ne_top)
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.holds, he, h]

/-- An assignment with a top trace extends to solve the chain encoding. -/
theorem topChainN_extend (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ x) ν = DeciNSSE.Tree.top) : Covariant.Sat (extend ρ x y ν) (topChainN x ν) := by
  apply (Covariant.sat_append _ _ _).mpr
  constructor
  · exact lowerStepsN_sat _ _ _ _ _ (extend_xv ρ x y ν) (extend_bv ..)
      (by rw [h]; exact DeciNSSE.Tree.top_ne_bot)
  · have he := extend_xv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simp [Covariant.Sat, Covariant.holds, he, h]

/-- An assignment with a nontop trace extends to solve the chain encoding. -/
theorem noTopChainN_extend (ρ : V k → DeciNSSE.Tree n) (x y : V k) (ν : List (Fin n))
    (h : trace (ρ y) ν ≠ DeciNSSE.Tree.top) : Covariant.Sat (extend ρ x y ν) (noTopChainN y ν) := by
  apply (Covariant.sat_append _ _ _).mpr
  constructor
  · exact upperStepsN_sat _ _ _ _ _ (extend_yv ρ x y ν) (extend_tv ..) h
  · have he := extend_yv ρ x y ν ν.length le_rfl
    simp only [List.take_length] at he
    simpa [Covariant.Sat, Covariant.holds, he, Function.comp_def, le_node_top_iff] using h

end Spines
end DeciENSSE.Support
