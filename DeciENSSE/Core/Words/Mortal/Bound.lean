import DeciENSSE.Core.Words.Mortal.Depth
import DeciENSSE.Anchored.ElementaryBound

/-! # Elementary mortal-hole bound

The separator reader has `N = 1 + ac + bd + ad` states for state counts `a`, `b`, `c`, `d`.
A mortal separator word has depth at most `2Na - 1`. Applying the elementary anchored
length bound at that depth supplies the bound used by `Self.exists_short_mortalHole`.

## Main declarations

- `mortalHoleBound`: the elementary anchored bound for the separator reader.
-/

namespace DeciENSSE.Core.Words.Mortal
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.HierarchyDepth
  DeciNSSE.Holes DeciNSSE.RejectedTail DeciENSSE.Anchored

/-- The mortal bound for state counts `a`, `b`, `c`, `d` of `A`, `B`, `A'`, `B'`: the
elementary anchored bound for the Π-reader, which has `N = 1 + ac + bd + ad` states, at the
depth `2 N a - 1`. -/
def mortalHoleBound (a b c d : ℕ) : ℕ :=
  let N := 1 + a * c + b * d + a * d
  anchoredLengthBound N (2 * N * a - 1)

end DeciENSSE.Core.Words.Mortal
