# Decidability of existential non-structural subtype entailment

**Existential non-structural subtype entailment is decidable for bottom, top
and one constructor of any finite arity and any variance, and for bottom and
one covariant constructor of any finite arity, over arbitrary, regular and
finite trees.** This repository gives a self-contained proof in
[Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), with computable
decision procedures for every signature and tree class, including arity zero.

Existential entailment `φ ⊨ ∃ z̄. ψ` asks whether every solution of a finite
conjunction `φ` of subtype constraints extends, by some choice of trees for the
*hidden* variables `z̄`, to a solution of a second conjunction `ψ`. The
variables of `φ` are *visible*; `ψ` may mention both kinds. Each decider below
(namespace `DeciENSSE`) has a correctness theorem without premises, named by
appending `_correct`.

| Signature | Variance of `f` | Tree classes | Deciders |
| --- | --- | --- | --- |
| `{⊥, f, ⊤}`, arity `n ≥ 0` | any `c : Fin n → Bool` | arbitrary, regular, finite | `decideExistsEntailsAny`, `decideExistsEntailsAnyReg`, `decideExistsEntailsAnyFin` |
| `{⊥, f}`, arity `n ≥ 0` | covariant | arbitrary, regular, finite | `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin` |

**Why it matters.** Type inference with subtyping produces *constrained types*
`∀ᾱ. C ⇒ τ`, and practical systems simplify their constraints. Semantic
subsumption between constrained types in the sense of Trifonov and Smith (1996)
is, with the quantified variables renamed apart, an existential entailment,

```text
∀ᾱ. C₁ ⇒ τ₁  ≤  ∀β̄. C₂ ⇒ τ₂      iff      C₂ ⊨ ∃ᾱ. (C₁ ∧ τ₁ ≤ τ₂),
```

and replacing a system `C(x̄, z̄)` by `D(x̄, k̄)`, where `x̄` remain observable,
is correct when `C ⊨ ∃k̄. D` and `D ⊨ ∃z̄. C`. Read as an inclusion of projected
solution sets, the problem is also called *restricted entailment* (Flanagan and
Felleisen 1999; Su and Aiken 2001). For non-structural subtyping it has been
open since 1996. The arrow is the binary constructor with a contravariant
domain, so the theorem covers subsumption of constrained types over `⊥`, `→`
and `⊤`, with no restriction on the polarity of the variables.

**Plain entailment as a corollary.** Non-structural subtype entailment (NSSE),
`φ ⊨ x ≤ y`, is the case with no hidden variables and the consequent `x ≤ y`.
[NSSE.lean](DeciENSSE/NSSE.lean) defines `decideEntails`, `decideEntailsReg`
and `decideEntailsFin` with the same names and types as the three deciders of
[deci-nsse](https://github.com/noti0na1/deci-nsse), in namespace `DeciENSSE`.
They call the existential deciders through `nsse_iff_ensse` and its two
variants and use no NSSE decision procedure. The same file decides plain
entailment over trees without top for a covariant constructor.

The library `DeciNSSE` is shared with deci-nsse and keeps its names: trees,
constraints, satisfiability, readers, holes, the block hierarchy, the
elementary hole bound and the rejected-tail decision. Its NSSE-only parts
(monitor deciders, solver, certificates, countermodels, complexity) remain in
deci-nsse. The existential proof is the library `DeciENSSE`. A paper with the
mathematical proof, its complexity bounds and applications is in preparation;
the formal proof follows its route except for the signature `{⊥, f}`.

## The problem

### Trees and the order

Labels are ordered `⊥ < f < ⊤`. A tree `DeciNSSE.Tree n` labels paths over
`Fin n`: the root exists, and exactly the constructor nodes have `n` children.
Trees may be infinite. A variance `c : Fin n → Bool` makes argument `i`
covariant (`false`) or contravariant (`true`), and `polarity c w` is the parity
of the contravariant letters of a path `w`. The order `Tree.Le c` compares the
labels at every path present in both trees, reversed at odd polarity; it is the
greatest relation with (`Characterization.treeLe_eq_gfp`)

```text
⊥ ≤ t ≤ ⊤                 for every tree t
f(a) ≤ f(b)               iff a(i) ≤ b(i) when c(i) = false
                          and b(i) ≤ a(i) when c(i) = true
```

The order is *non-structural*: `⊥ ≤ f(a) ≤ ⊤` although the extreme trees have
only a root. The arrow is `n = 2` with `c = ![true, false]`. See the
[deci-nsse README](https://github.com/noti0na1/deci-nsse) for more detail.

### Constraints, visible and hidden variables

A conjunction `EConstraint n k` is a list of literals `ELit n k` over the
variables `V k = Fin k`, of five forms:

| Literal | Lean | Holds under `ρ` when |
| --- | --- | --- |
| `x ≤ y` | `.le x y` | `Tree.Le c (ρ x) (ρ y)` |
| `x ≤ f(a)` | `.leF x a` | `Tree.Le c (ρ x) (Tree.node (ρ ∘ a))` |
| `f(a) ≤ x` | `.fLe a x` | `Tree.Le c (Tree.node (ρ ∘ a)) (ρ x)` |
| `x = ⊥` | `.eqBot x` | `ρ x = Tree.bot` |
| `x = ⊤` | `.eqTop x` | `ρ x = Tree.top` |

Here `a : Fin n → V k` selects the child variables, and `ESat c ρ φ` says that
`ρ` satisfies every literal of `φ`. Unlike the flat literals `Lit` of
deci-nsse, the variable inequality `x ≤ y` is primitive; in a consequent it
relates visible and hidden variables.

The antecedent `φ : EConstraint n k` has the `k` visible variables. The
consequent `ψ : EConstraint n (k + h)` has the visible variables first and then
`h` hidden ones: the visible `x` is `Fin.castAdd h x` and the hidden `z` is
`Fin.natAdd k z`. With `join ρ σ` combining the two assignments in this order,

```lean
def ExistsEntailsAny {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ, ESat c ρ φ → ∃ σ : V h → Tree n, ESat c (join ρ σ) ψ
```

A visible variable that does not occur in `φ` is unconstrained. Nested type
expressions reduce to flat literals by naming every compound subterm with a
fresh variable, visible in `φ` and hidden in `ψ`; this preserves the answer in
every tree class, but the preprocessing is not part of the formal development.

### Tree classes and vacuity

| Class | Meaning | Lean values | Semantics |
| --- | --- | --- | --- |
| Arbitrary | all finite and infinite trees | `Tree n` | `ExistsEntailsAny c φ ψ` |
| Regular | finitely many distinct subtrees | unfoldings of `RGraph n` | `ExistsEntailsAnyReg c φ ψ` |
| Finite | finitely many nodes | images of `FTree n` | `ExistsEntailsAnyFin c φ ψ` |

In each class the visible and the hidden assignments both range over the
class. If `φ` has no solution in the class, the entailment holds vacuously; if
`φ` has one and `ψ` has none, it fails. The classes differ: for `n = 1`, the
empty antecedent and the hidden equation `z = f(z)`, written as `z ≤ f(z)` and
`f(z) ≤ z`, the entailment holds over arbitrary and regular trees, with the
infinite tree `f(f(…))` as witness, and fails over finite trees
(`Examples.unaryCycle_classes`).

### An example

Let `f` be binary and covariant, and take the consequent

```text
ψ = x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z),      x, y visible, z hidden.
```

The literal `z ≤ f(z, z)` puts every subtree of `z` below `z`, so `∃z. ψ`
holds exactly when every subtree of `x` lies below `y`: an infinite family of
plain entailments, with a witness for `z` that depends on the solution. The
antecedent `x ≤ y` does not entail it, as `x = y = f(f(⊥, f(⊥, ⊥)), ⊥)` shows;
`x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` entails it, with the witness `z = x`.

### Two signatures

Over `{⊥, f}` the trees have no label `⊤` and the constraints no literal
`x = ⊤`: the syntax is `BFLit` and `BFConstraint`, the order is covariant, and
`ExistsEntails`, `ExistsEntailsReg` and `ExistsEntailsFin` require both
assignments to be `TopFree`. This is not the `{⊥, f, ⊤}` problem with `x = ⊤`
left out: with `x` visible and `φ` empty, `∃z̄. x ≤ f(z̄)` holds over `{⊥, f}`
(take the children of `x`, or `⊥` if `x = ⊥`) but fails over `{⊥, f, ⊤}` at
`x = ⊤`.

Whether existential entailment over `{⊥, f}` is decidable when `f` has a
contravariant argument is open. Then the sign of a leaf `⊥` depends on the
polarity of its path, and the reduction of the covariant case to `{⊥, f, ⊤}`
breaks down: `y ≤ f(y, …, y)` no longer forces `y` to be free of `⊤` (the arrow
tree `y = ⊤ → ⊥` satisfies `y ≤ y → y`).

## Formal statements

Import `DeciENSSE` for the whole development. The names below are in namespace
`DeciENSSE` with `open DeciNSSE`; arity and variable counts are inferred. The
deciders are `@[instance_reducible] def`s rather than instances, since several
decide related propositions; install one with `letI` or pass it to `@decide`.

### The six existential deciders

```lean
-- {⊥, f, ⊤}: any arity n ≥ 0 and any variance c
def decideExistsEntailsAny {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntailsAny c φ ψ)
def decideExistsEntailsAnyReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntailsAnyReg c φ ψ)
def decideExistsEntailsAnyFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntailsAnyFin c φ ψ)

-- {⊥, f}: any arity n ≥ 0, f covariant, top-free trees
def decideExistsEntails {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntails φ ψ)
def decideExistsEntailsReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsReg φ ψ)
def decideExistsEntailsFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsFin φ ψ)
```

None needs satisfiability, positive arity or an inhabited type. Each
correctness theorem takes the same arguments and states, for example,
`@decide _ (decideExistsEntailsAny c φ ψ) = true ↔ ExistsEntailsAny c φ ψ`.

### Plain entailment

A conjunction `φ : Constraint n k` of deci-nsse embeds as `liftConstraint φ`,
and `query x y : EConstraint n (k + 0)` is the literal `x ≤ y` with no hidden
variables. The three reductions are

```lean
theorem nsse_iff_ensse {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k) (x y : V k) :
    Entails c φ x y ↔ ExistsEntailsAny (h := 0) c (liftConstraint φ) (query x y)
theorem nsseReg_iff_ensseReg {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsReg c φ x y ↔ ExistsEntailsAnyReg (h := 0) c (liftConstraint φ) (query x y)
theorem nsseFin_iff_ensseFin {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsFin c φ x y ↔ ExistsEntailsAnyFin (h := 0) c (liftConstraint φ) (query x y)
```

and the three NSSE deciders built from them are

```lean
def decideEntails {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.Entails c φ x y)
def decideEntailsReg {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsReg c φ x y)
def decideEntailsFin {n k : ℕ} (c : Fin n → Bool)
    (φ : Constraint n k) (x y : V k) : Decidable (DeciNSSE.EntailsFin c φ x y)
```

For a covariant constructor over trees without top, `decideEntailsTopFree` and
its two variants decide `EntailsTopFree φ x y` and its regular and finite
variants, through `topFree_nsse_iff_ensse` and its two variants.

### API map

| Decider | Semantics | Correctness theorem | Module |
| --- | --- | --- | --- |
| `decideExistsEntailsAny` | `ExistsEntailsAny c φ ψ` | `decideExistsEntailsAny_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsAnyReg` | `ExistsEntailsAnyReg c φ ψ` | `decideExistsEntailsAnyReg_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsAnyFin` | `ExistsEntailsAnyFin c φ ψ` | `decideExistsEntailsAnyFin_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntails` | `ExistsEntails φ ψ` | `decideExistsEntails_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsReg` | `ExistsEntailsReg φ ψ` | `decideExistsEntailsReg_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsFin` | `ExistsEntailsFin φ ψ` | `decideExistsEntailsFin_correct` | [Main](DeciENSSE/Main.lean) |
| `decideEntails` | `DeciNSSE.Entails c φ x y` | `decideEntails_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsReg` | `DeciNSSE.EntailsReg c φ x y` | `decideEntailsReg_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsFin` | `DeciNSSE.EntailsFin c φ x y` | `decideEntailsFin_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFree` | `EntailsTopFree φ x y` | `decideEntailsTopFree_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFreeReg` | `EntailsTopFreeReg φ x y` | `decideEntailsTopFreeReg_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFreeFin` | `EntailsTopFreeFin φ x y` | `decideEntailsTopFreeFin_correct` | [NSSE](DeciENSSE/NSSE.lean) |

The semantics are defined in [Semantics.lean](DeciENSSE/Semantics.lean),
[Constraints/Basic.lean](DeciNSSE/Constraints/Basic.lean) and
[NSSE.lean](DeciENSSE/NSSE.lean). Below this interface,
`Core.Main.decideExistsEntailsAny` and its five companions take variables in
arbitrary finite types `X` and `X ⊕ Z`, connected to it by `toCoreFull`,
`splitFull`, `toCoreBF`, `splitBF`, `existsEntailsAny_iff_core`,
`existsEntails_iff_core` and their variants. [Examples.lean](DeciENSSE/Examples.lean)
proves `Examples.hiddenExtension`, `Examples.noInstance` and the class
separation above, and evaluates the deciders in the kernel at arity zero
(`Examples.nullary_yes`, `Examples.nullary_no`).

## Proof overview

The proof works with `{⊥, f, ⊤}` over arbitrary trees, reduces failures of the
entailment to holes of finite readers, bounds the length of a shortest hole,
and transfers the result to the other tree classes; every step is proved in
Lean.

1. **Arity zero.** The only trees are `⊥ < f() < ⊤` and the classes coincide;
   [Core/Nullary](DeciENSSE/Core/Nullary.lean) enumerates the assignments, and
   [Core/Main](DeciENSSE/Core/Main.lean) dispatches on the arity.

2. **Leaf cones and three conditions.** A tree is described by two *leaf
   cones*: the words whose path meets a leaf of sign 0, and those whose path
   meets a leaf of sign 1, where the sign combines the label `⊥` or `⊤` with
   the polarity of the path. The order adds leaves of sign 0 and removes
   leaves of sign 1 (`Core.Mixed.leGen_iff_leaf`), and every system becomes a
   Horn system with unary rules: moves that copy, push or pop the first letter
   of a word, facts, and forbidden roots, besides the exclusion of opposite
   atoms. Least models are closures of seeds, and colliding derivations can be
   merged. So, if both systems are satisfiable, the entailment holds iff three
   conditions on single seeds hold
   (`Core.Mixed.three_conditions_mixed`): **(I0)** every visible atom forced by
   `ψ` is forced by `φ`; **(U)** `ψ` derives no forbidden root from an atom
   live in `φ`; **(II)** every visible atom that `ψ` derives from such an atom
   lies in its closure under `φ` ([Core/Mixed](DeciENSSE/Core/Mixed): Leaf,
   LeafHorn, Duality, Conditions).

3. **Automata and self events.** Over signed variables the moves form a
   pushdown system, summarized by an *upper* automaton for pops and a *lower*
   one for pushes. Finite-state searches decide satisfiability and (I0).
   Variance adds a new way for an atom to be dead, a *self event*: a comparison
   of one word with its own suffixes whose automaton states are related
   (Signed, Membership, Sat, CondI).

4. **Holes for (U) and (II).** A *reader* is a finite automaton with rejected
   states and an admission relation on pairs of states; a *comparison* of `w`
   is a pair of cuts `s < e` with `w.drop e` a prefix of `w.drop s`; a *hole*
   is a rejected word without an admitted comparison. The failures of (U) are
   the holes of a *unit reader* that admits the self events, decided by
   `RejectedTail.decideHole` ([Units](DeciENSSE/Core/Mixed/Units.lean)). Under
   (U), (II) fails iff an extracted *two-word instance* has a hole: a safe
   *spine* word and a *target* word with a rejected cut, a comparison of equal
   suffixes carrying a head pair, and no guarded cross comparison or self event
   up to the first rejected cut ([Extract](DeciENSSE/Core/Mixed/Extract.lean),
   `Core.Mixed.mixed_reduction`). Extracted instances have *forced target
   heads*, which the bounds below need.

5. **Holes that are not mortal.** After the first rejected cut of the target
   both words share a suffix, which keeps an event only by continuing it
   periodically. From a *branching* spine state a continuation breaking every
   such obligation exists by the Fine–Wilf theorem; from a *thin* one, long
   continuations follow finitely many lassos, and a pump shortens the purely
   periodic ones. These holes have length polynomial in the state counts. In
   the remaining *mortal* case the spine has no infinite safe continuation
   ([Core/Words](DeciENSSE/Core/Words): NonMortal, NonMortalLasso, Periodic,
   NonMortalBound, Pump, and `Self/`).

6. **Mortal holes and anchored compression.** A mortal hole `(u, t)` becomes
   one *separator word* `u ♯ t`; its events become comparisons, and its head
   event an *anchored* comparison, whose matched factor ends right before the
   separator ([Mortal](DeciENSSE/Core/Words/Mortal)). Its rejected tail is
   short, so the library's depth theorem bounds its depth. Plain bounded-depth
   compression may delete the letters an anchored comparison depends on; a
   *positive channel* records an anchored witness at every level of the block
   hierarchy and is compared before letters are merged or columns deleted, so
   every shortening keeps a witness ([Anchored](DeciENSSE/Anchored),
   `Anchored.exists_short_posHole_elementary`). With step 5 this gives the
   short-hole theorem `Core.shortHoleBoundS` for every finite alphabet, and
   the decider tests satisfiability, (I0) and (U) and then searches every
   extracted instance below that bound ([Mixed/Final](DeciENSSE/Core/Mixed/Final.lean)).

7. **Regular and finite trees, by pinning and medians.** A failed extension of
   a solution of `φ` is retained by at most two visible observations
   (`Core.Mixed.two_observations_mixed`), each a finite ground bound. A
   satisfiable system with ground bounds has a regular solution, and graph
   equations pin visible regular values, so regular and arbitrary entailment
   coincide (`Core.Mixed.existsEntailsTReg_iff_mixed`). A system with a finite
   solution that is satisfiable with finitely many ground bounds has a finite
   solution satisfying them (`Core.Mixed.finiteBoundPinningMixed`): pass to
   signed variables, encode path pins by ranked chains of fresh variables, and
   restore sign symmetry by a median of three finite assignments. Hence finite
   entailment holds iff `φ` has no finite solution, or `ψ` has one and
   arbitrary entailment holds (`Core.Mixed.existsEntailsTFin_iff_mixed`).

8. **The signature `{⊥, f}`.** For a covariant constructor every leaf of a
   top-free tree is `⊥`, so a tree is its prefix-closed set of constructor
   positions. The covariant core ([Core](DeciENSSE/Core): Basic, Horn,
   Automata, AutomataDecide, Reduction, Decide, Final, Classes) proves three
   conditions in this picture, without self events (`Core.three_conditions`),
   reduces the third to two-word holes (`Core.ss2_reduction`), decides it with
   `Core.shortHoleBound`, and transfers it to regular and finite trees by
   regular Horn hulls and finite least solutions;
   [Full/Bridge](DeciENSSE/Core/Full/Bridge.lean) identifies these trees with
   the top-free trees (`Core.Full.bfEquivTopFree`). The paper instead reduces
   covariant `{⊥, f}` to `{⊥, f, ⊤}` by adding `v ≤ y_v` and
   `y_v ≤ f(y_v, …, y_v)` for every variable `v`.

## Scope

**Decidability in principle.** The deciders are computable definitions with
compiled code that run finite searches justified by proved bounds; classical
reasoning enters the proofs of the bounds and of correctness, not the
searches. The bounds are far too large for practical type inference, the
examples evaluate the deciders only at arity zero, and the deciders return
only the answer, not a counterexample word or a countermodel.

**Bounds proved in Lean.** Every search bound is an explicit function of the
state counts of the automata involved.

- *Anchored compression* (`Anchored.exists_short_posHole_elementary`): a
  positive hole of depth at most `d` of a monitor with `N` cores has one of
  length at most `Anchored.anchoredLengthBound N d`, and
  `Anchored.anchoredLengthBound_le` proves, with `Ξ = Anchored.anchoredExponent N d`,

  ```text
  anchoredLengthBound N d ≤ 2^(2^(5 Ξ + 6)),   Ξ = 6N² + 10N(N + d)(d + 1) + 7N + 3d + 4.
  ```
- *Mortal holes* (`Core.Mortal.exists_short_mortalHole`): for spine, target
  and head automata with `a`, `b`, `a'`, `b'` states, some mortal hole has a
  separator word of length at most `Core.mortalHoleBound a b a' b'`, that is,
  `anchoredLengthBound N (2 N a - 1)` with `N = 1 + a a' + b b' + a b'`.
- *Holes that are not mortal*: `Core.pumpHoleBound`, polynomial in the four
  state counts (`Core.nonMortalShortHoleBound_poly`).
- *Condition (U)*: `DeciNSSE.RejectedTail.holeLengthBound N`, at most
  `2^(2^(1280 (N + 1)^5))` for a reader with `N` states
  (`DeciNSSE.RejectedTail.holeLengthBound_le`).

**Not mechanized.** The paper's results beyond decidability are not formalized
here: flattening, the bound `2^(2^(2^(16 s + 18)))` on counterexample words in
terms of the number `s` of variables, the effective construction of
countermodels, the 2-EXPSPACE upper bound by a search over compression
summaries, membership in PSPACE for `n ≤ 1`, the exponential lower bound on
shortest counterexamples, and PSPACE-hardness for every fixed arity `n ≥ 2`.
The theorem covers one constructor; several constructors, entailment of
disjunctions and `{⊥, f}` with a contravariant argument are not covered.

## Relation to previous work

- Plain NSSE was posed as an open problem in 1996 by Rehof
  ([TLCA problem 16](https://tlca.di.unito.it/opltlca/opltlcasu23.html)); it is
  decided for one constructor of any arity and variance by
  [deci-nsse](https://github.com/noti0na1/deci-nsse).
- Trifonov and Smith (1996) defined subsumption of constrained types over
  regular trees with `→`, `⊥` and `⊤`, left its decidability open and decided
  a sound approximation. Fähndrich and Aiken (1996) noted that no complete
  algorithm was known, Su (2002) that virtually nothing was known beyond the
  lower bounds from entailment and that the problem might be undecidable, and
  Priesnitz (2004) called it a prominent open problem.
- The first-order theory of non-structural subtyping is undecidable, already
  over `{⊥, f}` with `f` binary and covariant, in all three tree classes (Su,
  Aiken, Niehren, Priesnitz and Treinen 2002), with six quantifier blocks and
  a matrix with disjunctions and negations; existential entailment has one
  alternation and conjunctions on both sides.
- Over feature trees existential entailment is PSPACE-complete (Müller,
  Niehren and Treinen 1998, 2001), in a setting where a fresh feature is always
  available; a constructor of fixed arity offers no fresh direction.
- Flanagan and Felleisen (1999) decide restricted entailment in exponential
  time and show PSPACE-hardness, over a set-based domain of complete infinite
  trees with total selectors, so their procedure does not apply here.

**Relation to deci-nsse.** Condition (U) is a hole problem of deci-nsse's
kind, decided by its `RejectedTail.decideHole`, and the depth of a mortal
separator word is bounded by its `RejectedTail.rejected_depth`. New here are
the leaf-cone characterization, self events, two-word holes with their pump,
and anchored compression. For plain entailment, deci-nsse reduces to holes
through its spine monitors, this repository through the existential
characterization.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The package pins Lean and Mathlib to **v4.35.0**. The first command downloads
compiled Mathlib dependencies; the second checks both libraries, `DeciNSSE`
and `DeciENSSE`. There are no executables.

To inspect the logical dependencies, save the following as `Check.lean` and
run `lake env lean Check.lean`:

```lean
import DeciENSSE

#print axioms DeciENSSE.decideExistsEntailsAny_correct
#print axioms DeciENSSE.decideExistsEntailsAnyReg_correct
#print axioms DeciENSSE.decideExistsEntailsAnyFin_correct
#print axioms DeciENSSE.decideExistsEntails_correct
#print axioms DeciENSSE.decideExistsEntailsReg_correct
#print axioms DeciENSSE.decideExistsEntailsFin_correct
#print axioms DeciENSSE.decideEntails_correct
#print axioms DeciENSSE.decideEntailsReg_correct
#print axioms DeciENSSE.decideEntailsFin_correct
#print axioms DeciENSSE.decideEntailsTopFree_correct
#print axioms DeciENSSE.decideEntailsTopFreeReg_correct
#print axioms DeciENSSE.decideEntailsTopFreeFin_correct
```

These theorems use only the usual `propext`, `Classical.choice` and
`Quot.sound`. Lean's kernel checks their proof terms; running the compiled
deciders also relies on the compiler.

## Repository layout

The shared library has 54 Lean files under `DeciNSSE/` and the existential
proof 77 files under `DeciENSSE/`, with 11,687 and 23,527 lines including the
root modules `DeciNSSE.lean` and `DeciENSSE.lean`, which import every module of
their library; the counts include comments, docstrings and examples.
Namespaces are relative to `DeciNSSE` or `DeciENSSE`; "top level" means the
root namespace itself.

### `DeciNSSE/`: the shared library

| Module | Namespace | Purpose |
| --- | --- | --- |
| [Words](DeciNSSE/Words.lean) | `Words` | Finite-alphabet paths, powers and periods |
| [Semantics](DeciNSSE/Semantics): Sym, Tree, Finite, Regular, Order, Normalization, Safety | top level, `Sym`, `Tree`, `FTree`, `RGraph`, `Safety` | Labels, trees, finite terms, regular graphs, the variance order, normalization, finite witnesses to order failure |
| [Semantics](DeciNSSE/Semantics): Selector, Characterization | `SignSelection`, `Characterization` | Polarity selection for signed solutions; fixed points and representation of the tree classes |
| [Constraints](DeciNSSE/Constraints): Basic, Closure, Dual, PathBounds, Signed | top level, `Covariant`, `Closure`, `ConstraintDual`, `PathBounds` | Flat syntax, satisfaction, plain entailment, closure, duals, path bounds, the signed translation |
| [Satisfiability](DeciNSSE/Satisfiability): LeastShape, ShapeGraph, Cycle, Finite, FiniteVariance, Decide | top level, `RGraph`, `FiniteSat`, `FiniteVariance`, `PathDecision` | Least shapes and their graphs, label and cycle clashes, satisfiability over arbitrary and finite trees |
| [Transfer/RankedExtension](DeciNSSE/Transfer/RankedExtension.lean) | `Ranked` | Ranked source and sink extensions |
| [Holes/Basic](DeciNSSE/Holes/Basic.lean) | `Holes` | Readers, comparisons and holes |
| [Holes/Hierarchy](DeciNSSE/Holes/Hierarchy.lean) and [Holes/Hierarchy/](DeciNSSE/Holes/Hierarchy): Expansion, Derived, Canonical, Starts, Unary, Reader | `LetteredHierarchy` | The canonical block hierarchy, derived monitors, unary levels, readers as lettered monitors |
| [Holes](DeciNSSE/Holes): Depth, Cores, StartCores, CoreOccurrences, Supports | `HierarchyDepth`, `Cores`, `StartCores`, `CoreOccurrences`, `Supports` | Canonical depth, cores and supports of hierarchy levels |
| [Holes](DeciNSSE/Holes): Packets, Desubstitution, CoAlignment, Exchange, LevelMaps, NormalForm, BoundaryPairs | `Packets`, `Desubstitution`, `CoAlignment`, `CoAlignment.Lettered`, `LevelMaps`, `NormalForm`, `BoundaryPairs` | Block tuples, marker codes, comparison alignment, exchange types, the isolated-letter normal form, boundary pairs |
| [Holes](DeciNSSE/Holes): Agree, Columns, BoundedDepth, ElementaryBound | `BoundedDepth`, `ElementaryBound` | The column automaton, compression at bounded depth, elementary dictionary and length bounds |
| [RejectedTail](DeciNSSE/RejectedTail) | `RejectedTail` | Rejected-path property, linear tail, return gap, depth bound, the finite hole search `decideHole` |

### `DeciENSSE/`: existential entailment

| Module | Namespace | Purpose |
| --- | --- | --- |
| [Semantics](DeciENSSE/Semantics.lean), [Main](DeciENSSE/Main.lean) | top level | Public syntax and semantics, conversions to the core, the six existential deciders |
| [NSSE](DeciENSSE/NSSE.lean) | top level | Plain entailment: reductions, NSSE deciders and the top-free variants |
| [Examples](DeciENSSE/Examples.lean) | `Examples` | Small proved and evaluated instances |
| [Core/Main](DeciENSSE/Core/Main.lean), [Core/Nullary](DeciENSSE/Core/Nullary.lean), [Support/Nullary](DeciENSSE/Support/Nullary/Decide.lean) | `Core.Main`, `Core.Nullary`, `Support.Nullary` | Deciders over finite carriers, dispatch on the arity, enumeration at arity zero |
| [Core](DeciENSSE/Core): Basic, Horn, Automata, AutomataDecide | `Core`, `Core.Bound` | `{⊥, f}`: trees as constructor sets, Horn characterization, upper and lower automata, the first two conditions |
| [Core](DeciENSSE/Core): Reduction, Decide, Final, ClassesLanguage, Classes | `Core`, `Core.Classes` | `{⊥, f}`: two-word instances, bounded search, the three classes |
| [Core/Full](DeciENSSE/Core/Full): Basic, Bridge | `Core.Full` | Full-signature syntax over arbitrary carriers; bottom-only versus top-free trees |
| [Core/Mixed](DeciENSSE/Core/Mixed): Leaf, LeafHorn, Duality, Conditions | `Core.Mixed` | Leaf cones, the Horn presentation, duality and deadness, the three conditions |
| [Core/Mixed](DeciENSSE/Core/Mixed): Signed, Membership, Sat, CondI, Units | `Core.Mixed` | Pushdown automata, self events, satisfiability, conditions (I0) and (U) |
| [Core/Mixed](DeciENSSE/Core/Mixed): Extract, Decide, Final | `Core.Mixed`, `Core.SS2Self` | Two-word instances with self events, bounded search, the arbitrary-tree decider |
| [Core/Mixed](DeciENSSE/Core/Mixed): Regular, Finite, FinitePinning, FinitePinningSigned | `Core.Mixed`, `Core.Mixed.FinitePinning` | Two observations, regular and finite transfer, finite-bound pinning by medians |
| [Core/Full](DeciENSSE/Core/Full): AC, Observations, ACPins, Classes, Flatten, TopGraphs, Pinning, PinningGround, PinningSpines | `Core.Full`, `Core.Full.AC`, `Core.Full.Flatten`, `Core.Full.TopGraphs`, `Core.Full.Pinning` | Observations and ground bounds, flattening and finite satisfiability, graph equations, covariant finite pinning |
| [Support](DeciENSSE/Support): Variance, TransferFin, Transfer, VarianceReg, Semantics | `Support`, `Support.FinT`, `Support.Ranked`, `Support.Spines`, `Support.RGraphN` | Tree medians, finite medians, spine chains, ranked extensions, regular satisfiability |
| [Core/Words](DeciENSSE/Core/Words): LDFA, SS2, Statements, Transport | `Core`, `Core.SS2`, `Core.LDFA` | Automata over arbitrary alphabets, two-word hole instances, statements of hole bounds |
| [Core/Words](DeciENSSE/Core/Words): NonMortal, NonMortalLasso, Periodic, NonMortalBound, Pump, Bound | `Core`, `Core.SS2`, `Core.TwoTape` | Branching, thin and mortal cases, lassos, the pump, the combined bound |
| [Core/Words/Mortal](DeciENSSE/Core/Words/Mortal): SepWord, PiReader, Depth, Bound | `Core.Mortal`, `Core` | Separator words, the Π-reader, depth and length of mortal holes |
| [Core/Words/Self](DeciENSSE/Core/Words/Self): SS2Self, PumpS, NonMortalS, MortalS, BoundS | `Core`, `Core.SS2Self`, `Core.Mortal` | The same results with self events |
| [Anchored](DeciENSSE/Anchored): Channel, Desubstitution, Agree, Columns, Unary, NormalForm, ElementaryBound, Estimate | `Anchored` | Positive channels, anchored compression and its elementary bound |

## License

Apache License 2.0; see [LICENSE](LICENSE).
