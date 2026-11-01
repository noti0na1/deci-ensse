import DeciENSSE.Core.Words.Mortal.PiReader
import DeciNSSE.RejectedTail.Depth

/-! # Depth of mortal separator words

The separator word of a mortal hole is rejected by the Π-reader, and fewer than `|SA|`
letters follow its first rejected cut. By the return-gap depth bound for rejected words,
its canonical depth is at most `2 · |RState| · |SA| - 1`.

## Main declarations

- `mortal_depth`: the depth bound for separator words of mortal holes.
- `mortal_compression_input`: a mortal hole gives a Π-hole of the lettered monitor of the
  reader within this depth.

The declarations are in the namespace `DeciENSSE.Core.Mortal`.
-/

namespace DeciENSSE.Core.Mortal

variable {α : Type*} [Fintype α] [DecidableEq α]
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.HierarchyDepth
  DeciNSSE.RejectedTail

variable {SA SB SA' SB' : Type*} [Fintype SA] [Fintype SB]
  [Fintype SA'] [Fintype SB'] [DecidableEq SA] [DecidableEq SB]
  [DecidableEq SA'] [DecidableEq SB']
variable (I : SS2 α SA SB SA' SB')

/-- The separator word of a mortal hole has depth at most `2 · |RState| · |SA| - 1`. -/
theorem mortal_depth {u t : Word α} (h : I.IsMortalHole u t) :
    depth (sepWord u t) ≤
      2 * Fintype.card (State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) *
        Fintype.card SA - 1 := by
  obtain ⟨j,hj,ht⟩ := h.2.2
  have hj' : I.J t = some j := by simpa using hj
  have hfirst := first_rejected_cut I h.1.1 h.2.1 hj'
  have hr := (rejected_sep_iff I u t).mpr ⟨h.1.1,h.2.1,j,hj',ht⟩
  have hd := rejected_depth (reader I) (Rej I) (sepWord_ne_nil u t) hr hfirst
  have he : (sepWord u t).length - (u.length+1+j) = t.length-j := by
    simp only [length_sepWord]; omega
  rw [he] at hd
  exact hd.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (by omega :
    t.length-j+1 ≤ Fintype.card SA)) 1)

/-- A mortal hole gives a hole of the lettered monitor of the Π-reader with an anchored
comparison in `Pi`, within the depth bound. -/
theorem mortal_compression_input {u t : Word α} (h : I.IsMortalHole u t) :
    (ofReader (reader I) (Adm I) (Rej I)).IsHole (sepWord u t) ∧
      HasPi I (sepWord u t) ∧
      depth (sepWord u t) ≤
        2 * Fintype.card (State (SA := SA) (SB := SB) (SA' := SA') (SB' := SB')) *
          Fintype.card SA - 1 := by
  have hh := (ofReader_pi_iff I (sepWord u t)).mpr ⟨u,t,rfl,h⟩
  exact ⟨hh.1,hh.2,mortal_depth I h⟩

end DeciENSSE.Core.Mortal
