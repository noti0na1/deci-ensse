import DeciENSSE.Core.Full.Basic

/-! # Signed translation of full constraints

Each variable has positive and negative copies. Contravariant children switch
copies; the negative clause reverses the inequality and exchanges bottom and top.
This is the carrier-independent version of `DeciNSSE.signed`, with an additional
clause for variable inequalities. `Mixed.signedMovesLit` forgets the extreme-label
units to describe only the copy, push, and pop moves of the leaf automata.

## Main declarations

- `signedLit`: the two signed clauses of one full literal.
- `signed`: the complete covariant system on signed variables.
-/

namespace DeciENSSE.Core.Full
open DeciNSSE

variable {n : ℕ} {V : Type*}

/-- Two covariant literals, with contravariant children changing sign. -/
def signedLit (c : Fin n → Bool) : LitT n V → List (LitT n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .fle a u => [.fle (fun i => (a i, c i)) (u, false),
      .lef (u, true) (fun i => (a i, !(c i)))]
  | .lef u a => [.lef (u, false) (fun i => (a i, c i)),
      .fle (fun i => (a i, !(c i))) (u, true)]
  | .bot u => [.bot (u, false), .top (u, true)]
  | .top u => [.top (u, false), .bot (u, true)]

/-- Translate each flat literal into constraints on paired signed variables. -/
def signed (c : Fin n → Bool) (χ : List (LitT n V)) : List (LitT n (V × Bool)) :=
  χ.flatMap (signedLit c)

end DeciENSSE.Core.Full
