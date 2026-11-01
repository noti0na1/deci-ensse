import DeciENSSE.Core.Automata.Moves

/-! # Recognizing forced atoms, seed closures, and liveness

The lower automaton recognizes the least forced-atom closure. The upper
automaton checks liveness by avoiding bottom variables at every prefix.
Together their summaries characterize the closure of a single seed using
pairs of cuts and a prefix comparison of the remaining words.

This completes the covariant automata step: `satisfiable_iff` reduces
satisfiability to a finite root-clash test, and `cl_membership` supplies the
closure formula used to extract two-word instances in `Core/Reduction`.
Importing this module also exposes saturation, powerset automata, and move
factorization from `Core/Automata/{Saturation,Powerset,Moves}`.

## Main declarations

- `Automata.mu_membership`: the lower automaton recognizes forced atoms.
- `Automata.satisfiable_iff`, `Automata.decideSat`: finite satisfiability testing.
- `Automata.liveness`: live seeds are exactly upper-safe words, for a
  satisfiable system.
- `Automata.cl_membership`: the two-cut characterization of singleton closure.
-/

namespace DeciENSSE.Core
open DeciENSSE.Core.Words
namespace Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A lower-root hit persists backwards along prefixes. -/
theorem Q_fact_prefix {χ : List (Lit n V)} {y : V} {u t : List (Fin n)}
    (hp : u.IsPrefix t) (h : (Q χ y t ∩ LowF χ).Nonempty) :
    (Q χ y u ∩ LowF χ).Nonempty := by
  classical
  by_cases he : u = t
  · simpa [he] using h
  · have hlt : u.length < t.length := lt_of_le_of_ne hp.length_le (by
      intro hl; exact he (hp.eq_of_length hl))
    have hn : (Q χ y t).Nonempty := h.mono Finset.inter_subset_left
    have hc := cone_prefix hn hlt
    rw [← List.prefix_iff_eq_take.mp hp] at hc
    exact Finset.not_disjoint_iff_nonempty_inter.mp hc

/-- The lower automaton recognizes the least forced-atom closure. -/
theorem mu_membership {χ : List (Lit n V)} {y : V} {t : List (Fin n)} :
    (y, t) ∈ Mu χ ↔ (Q χ y t ∩ LowF χ).Nonempty := by
  constructor
  · rintro ⟨⟨r, w⟩, ⟨hw, as, hl⟩, hr⟩
    change w = [] at hw
    subst w
    obtain ⟨W, hm, hp⟩ := truncation.mp hr
    have hq : r ∈ Q χ y W := by
      apply (summaries_Q W []).mpr
      exact ⟨[], W, rfl, rfl, hm⟩
    exact Q_fact_prefix hp ⟨r, Finset.mem_inter.mpr ⟨hq, mem_LowF.mpr ⟨as, hl⟩⟩⟩
  · rintro ⟨r, hr⟩
    obtain ⟨hq, hl⟩ := Finset.mem_inter.mp hr
    obtain ⟨as, hl⟩ := mem_LowF.mp hl
    exact ⟨(r, []), ⟨rfl, as, hl⟩, by simpa using (Q_moves hq []).reach⟩

/-- Satisfiability is equivalent to absence of finite root clashes. -/
theorem satisfiable_iff (χ : List (Lit n V)) :
    (∃ ρ, Sat ρ χ) ↔ ∀ v ∈ Bot χ, Disjoint (down χ v) (LowF χ) := by
  rw [satisfiable_iff_mu_avoids]
  constructor
  · intro h v hv
    apply Finset.disjoint_left.mpr
    intro r hr hl
    exact h ((mu_membership (y := v) (t := [])).mpr
      ⟨r, Finset.mem_inter.mpr ⟨hr, hl⟩⟩) ⟨rfl, mem_Bot.mp hv⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨r, hr⟩ := mu_membership.mp ha
    exact Finset.disjoint_left.mp (h a.1 (mem_Bot.mpr hb))
      (by simpa [hw] using (Finset.mem_inter.mp hr).1) (Finset.mem_inter.mp hr).2

/-- Executable satisfiability over arbitrary {⊥, f} trees. -/
def decideSat (χ : List (Lit n V)) : Decidable (∃ ρ, Sat ρ χ) :=
  decidable_of_iff (∀ v ∈ Bot χ, Disjoint (down χ v) (LowF χ)) (satisfiable_iff χ).symm

/-- Safety includes every cut, including the starting and final state. -/
def Safe (χ : List (Lit n V)) (x : V) (u : List (Fin n)) : Prop :=
  ∀ j ∈ Finset.range (u.length + 1), Disjoint (P χ x (u.take j)) (Bot χ)
instance {χ : List (Lit n V)} {x : V} {u : List (Fin n)} : Decidable (Safe χ x u) :=
  inferInstanceAs (Decidable (∀ j ∈ Finset.range (u.length + 1),
    Disjoint (P χ x (u.take j)) (Bot χ)))

/-- Safety means that no upper prefix meets a bottom variable. -/
theorem safe_iff (χ : List (Lit n V)) (x : V) (u : List (Fin n)) :
    Safe χ x u ↔ ∀ j ≤ u.length, Disjoint (P χ x (u.take j)) (Bot χ) := by
  simp only [Safe, Finset.mem_range, Nat.lt_succ_iff]

/-- A seed is live exactly when every upper prefix avoids bottom variables. -/
theorem liveness {χ : List (Lit n V)} (hs : ∃ ρ, Sat ρ χ) (x : V) (u : List (Fin n)) :
    (x, u) ∈ Live χ ↔ Safe χ x u := by
  rw [live_iff_reach_avoids hs, safe_iff]
  constructor
  · intro h j hj
    apply Finset.disjoint_left.mpr
    intro b hb hbot
    have hm := (P_moves hb (u.drop j)).reach
    rw [List.take_append_drop] at hm
    exact h (hm.trans (by simpa using reach_truncate (χ := χ) b [] (u.drop j)))
      ⟨rfl, mem_Bot.mp hbot⟩
  · intro h a ha hn
    obtain ⟨hw, hb⟩ := hn
    obtain ⟨W, hm, _⟩ := truncation.mp ha
    obtain ⟨β, γ, σ, v, hu, _, hp, hq⟩ := moves_normal hm
    change u = β ++ σ at hu
    have hγ : γ = [] := by
      by_contra hne
      have hn : (Q χ a.1 γ).Nonempty := ⟨v, hq⟩
      have hc := cone_prefix hn (List.length_pos_iff.mpr hne)
      simp only [List.take_zero, Q_nil] at hc
      exact hc ((satisfiable_iff χ).mp hs a.1 (mem_Bot.mpr hb))
    have hp' : a.1 ∈ P χ x β := P_closed hp (by simpa [hγ] using hq)
    have hd := h β.length (by rw [hu]; simp)
    rw [hu, List.take_left] at hd
    exact Finset.disjoint_left.mp hd hp' (mem_Bot.mpr hb)

/-- Every prefix of a safe word is safe. -/
theorem safe_prefix {χ : List (Lit n V)} {x : V} {u t : List (Fin n)}
    (h : Safe χ x t) (hp : u.IsPrefix t) : Safe χ x u := by
  rw [safe_iff] at h ⊢
  intro j hj
  obtain ⟨v, rfl⟩ := hp
  simpa [List.take_append_of_le_length hj] using h j (by simp; omega)

/-- Singleton closure is described by summaries. The prefix comparison has no ordering condition
between its two cuts. -/
theorem cl_membership {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)} :
    (y, t) ∈ Cl χ (x, u) ↔ (Q χ y t ∩ LowF χ).Nonempty ∨
      ∃ s ≤ u.length, ∃ e ≤ t.length,
        (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty ∧
        (t.drop e).IsPrefix (u.drop s) := by
  constructor
  · rintro (hm | hr)
    · exact Or.inl (mu_membership.mp hm)
    · obtain ⟨W, hm, ht⟩ := truncation.mp hr
      obtain ⟨β, γ, σ, v, hu, hW, hp, hq⟩ := moves_normal hm
      change u = β ++ σ at hu
      change W = γ ++ σ at hW
      rw [hW] at ht
      by_cases hle : γ.length ≤ t.length
      · have hg : γ.IsPrefix t := List.prefix_of_prefix_length_le (List.prefix_append γ σ) ht hle
        obtain ⟨r, hr⟩ := hg
        rw [← hr] at ht
        have hs : r.IsPrefix σ := (List.prefix_append_right_inj γ).mp ht
        right
        refine ⟨β.length, by rw [hu]; simp, γ.length, hle, ?_, ?_⟩
        · simpa [hu, ← hr] using
            (show (P χ x β ∩ Q χ y γ).Nonempty from ⟨v, Finset.mem_inter.mpr ⟨hp, hq⟩⟩)
        · simpa [hu, ← hr] using hs
      · left
        have hlt : t.length < γ.length := by omega
        have htγ : t.IsPrefix γ := List.prefix_of_prefix_length_le ht
          (List.prefix_append γ σ) (by omega)
        have hc := cone_prefix (show (Q χ y γ).Nonempty from ⟨v, hq⟩) hlt
        rw [← List.prefix_iff_eq_take.mp htγ] at hc
        exact Finset.not_disjoint_iff_nonempty_inter.mp hc
  · rintro (hm | ⟨s, _, e, _, hv, hp⟩)
    · exact Or.inl (mu_membership.mpr hm)
    · obtain ⟨v, hv⟩ := hv
      obtain ⟨hpv, hqv⟩ := Finset.mem_inter.mp hv
      obtain ⟨r, hr⟩ := hp
      right
      have hm := ((P_moves hpv (u.drop s)).trans (Q_moves hqv (u.drop s))).reach
      rw [List.take_append_drop] at hm
      have he : t.take e ++ u.drop s = t ++ r := by
        rw [← hr, ← List.append_assoc, List.take_append_drop]
      rw [he] at hm
      exact hm.trans (reach_truncate y t r)

/-- A rejected final state guarantees that the first rejected cut exists. -/
theorem J_defined {χ : List (Lit n V)} {y : V} {t : List (Fin n)}
    (h : Disjoint (Q χ y t) (LowF χ)) : ∃ j, J χ y t = some j := by
  cases he : J χ y t with
  | some j => exact ⟨j, rfl⟩
  | none =>
    have hn : ∀ i ≤ t.length, ¬ Disjoint (Q χ y (t.take i)) (LowF χ) := by
      simpa [J, List.find?_eq_none, Nat.lt_succ_iff] using he
    exact (hn t.length le_rfl (by simpa using h)).elim

/-- All cuts contributing to closure membership lie at or before J. This includes cuts at J
itself. -/
theorem cl_cuts_before_J {χ : List (Lit n V)} {x y : V} {u t : List (Fin n)}
    {j s e : ℕ} (hj : J χ y t = some j) (he : e ≤ t.length)
    (h : (P χ x (u.take s) ∩ Q χ y (t.take e)).Nonempty) : e ≤ j := by
  by_contra hle
  rw [after_J hj (by omega) he] at h
  simp at h

end Automata
end DeciENSSE.Core
