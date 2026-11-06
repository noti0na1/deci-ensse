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
| `{⊥, f, ⊤}`, arity `n ≥ 0` | any `c : Fin n → Bool` | arbitrary, regular, finite | `decideExistsEntails`, `decideExistsEntailsReg`, `decideExistsEntailsFin` |
| `{⊥, f}`, arity `n ≥ 0` | covariant | arbitrary, regular, finite | `decideExistsEntailsTopFree`, `decideExistsEntailsTopFreeReg`, `decideExistsEntailsTopFreeFin` |

These deciders take flat constraints. Constraints between arbitrary type
expressions are decided by `decideExistsEntailsTerm` and its five variants, and
subsumption of constrained type schemes by `decideSubsumes` and its five
variants, for the same signatures, variances and tree classes.

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
and `⊤`, with no restriction on the polarity of the variables;
[Subsumption.lean](DeciENSSE/Subsumption.lean) proves the formula above, with
contexts, and decides subsumption.

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
deci-nsse. The existential proof is the library `DeciENSSE`.

The paper
[*Existential Subtype Entailment Is Decidable for Non-Structural Subtyping*](paper/main.pdf)
explains the mathematical proof in detail, with its complexity bounds and
applications. It is an unpolished write-up; its LaTeX sources are in
[paper](paper). The paper and the formal proof follow the same routes. Each
theorem, lemma, proposition and corollary of the paper outside its complexity
section has a Lean declaration in [DeciENSSE/Paper](DeciENSSE/Paper), named
after its label, as do several definitions and examples, and
[scripts/contract.py](scripts/contract.py) checks this correspondence (see
[scripts/README-contract.md](scripts/README-contract.md)); the appendix of the
paper lists it in a generated table. The section on complexity and sharper
bounds, with its appendix, is the part of the paper that is not mechanized.

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
def ExistsEntails {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) : Prop :=
  ∀ ρ, ESat c ρ φ → ∃ σ : V h → Tree n, ESat c (join ρ σ) ψ
```

A visible variable that does not occur in `φ` is unconstrained. Constraints
`e ≤ e'` and `e = e'` between nested type expressions
([Terms.lean](DeciENSSE/Terms.lean)) reduce to flat literals by naming every
distinct nonvariable subexpression with a fresh variable, visible in `φ` and hidden
in `ψ` ([Flattening.lean](DeciENSSE/Flattening.lean)). This preserves the
answer in every tree class that contains the values of the subexpressions, in
particular in all three classes below
(`Flattening.existsEntailsTermIn_iff_flatten`), and the flat systems have at
most six variable occurrences per symbol of the input
(`Flattening.flatSize_flatten_le`).

### Tree classes and vacuity

| Class | Meaning | Lean values | Semantics |
| --- | --- | --- | --- |
| Arbitrary | all finite and infinite trees | `Tree n` | `ExistsEntails c φ ψ` |
| Regular | finitely many distinct subtrees | unfoldings of `RGraph n` | `ExistsEntailsReg c φ ψ` |
| Finite | finitely many nodes | images of `FTree n` | `ExistsEntailsFin c φ ψ` |

In each class the visible and the hidden assignments both range over the
class. If `φ` has no solution in the class, the entailment holds vacuously; if
`φ` has one and `ψ` has none, it fails. The classes differ: for `n = 1`, the
empty antecedent and the hidden equation `z = f(z)`, written as `z ≤ f(z)` and
`f(z) ≤ z`, the entailment holds over arbitrary and regular trees, with the
infinite tree `f(f(…))` as witness, and fails over finite trees
(`Examples.unaryCycle_classes`; `Examples.cycle_classes` for every positive
arity and variance).

### An example

Let `f` be binary and covariant, and take the consequent

```text
ψ = x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z),      x, y visible, z hidden.
```

The literal `z ≤ f(z, z)` puts every subtree of `z` below `z`, so `∃z. ψ`
holds exactly when every subtree of `x` lies below `y`: an infinite family of
plain entailments, with a witness for `z` that depends on the solution. The
antecedent `x ≤ y` does not entail it, as `x = y = f(f(⊥, f(⊥, ⊥)), ⊥)` shows;
`x ≤ y ∧ x ≤ f(x, b) ∧ b = ⊥` entails it, with the witness `z = x`. Both claims
are proved in [Examples/Public](DeciENSSE/Examples/Public.lean), as
`Examples.subtree_not_entails` and `Examples.subtree_entails`, and over
`{⊥, f}` as `Examples.subtree_not_entails_topFree` and
`Examples.subtree_entails_topFree`. This is the running example of the paper;
[Examples/ShiftClosure](DeciENSSE/Examples/ShiftClosure.lean) proves its
characterizations by subtrees and by suffixes of constructor positions
(`Examples.shift_iff_subtrees`, `Examples.shift_iff_suffixes`).

### Two signatures

Over `{⊥, f}` the trees have no label `⊤` and the constraints no literal
`x = ⊤`: the syntax is `BFLit` and `BFConstraint` (embedded into the full
syntax by `BFLit.toELit`), the order is covariant, and `ExistsEntailsTopFree`,
`ExistsEntailsTopFreeReg` and `ExistsEntailsTopFreeFin` require both
assignments to be `TopFree`. This is not the `{⊥, f, ⊤}` problem with `x = ⊤`
left out: with `x` visible and `φ` empty, `∃z̄. x ≤ f(z̄)` holds over `{⊥, f}`
(take the children of `x`, or `⊥` if `x = ⊥`) but fails over `{⊥, f, ⊤}` at
`x = ⊤`. It reduces to the `{⊥, f, ⊤}` problem by the top-freeness gadget
`v ≤ y_v ∧ y_v ≤ f(y_v, …, y_v)` on every variable
([TopFree.lean](DeciENSSE/TopFree.lean)).

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
The module docstring of [Main.lean](DeciENSSE/Main.lean) contains a *proof
map* from each decider to the theorems it rests on.

### The six existential deciders

```lean
-- {⊥, f, ⊤}: any arity n ≥ 0 and any variance c
def decideExistsEntails {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntails c φ ψ)
def decideExistsEntailsReg {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntailsReg c φ ψ)
def decideExistsEntailsFin {n k h : ℕ} (c : Fin n → Bool)
    (φ : EConstraint n k) (ψ : EConstraint n (k + h)) :
    Decidable (ExistsEntailsFin c φ ψ)

-- {⊥, f}: any arity n ≥ 0, f covariant, top-free trees
def decideExistsEntailsTopFree {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFree φ ψ)
def decideExistsEntailsTopFreeReg {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeReg φ ψ)
def decideExistsEntailsTopFreeFin {n k h : ℕ} (φ : BFConstraint n k)
    (ψ : BFConstraint n (k + h)) : Decidable (ExistsEntailsTopFreeFin φ ψ)
```

None needs satisfiability, positive arity or an inhabited type. Each
correctness theorem takes the same arguments and states, for example,
`@decide _ (decideExistsEntails c φ ψ) = true ↔ ExistsEntails c φ ψ`. It is an
instance of `decide_eq_true_iff`: the substance is that the deciders are
ordinary computable definitions whose answers come from finite searches
justified by the proofs.

### Type expressions and constrained types

An expression `Term n V` is a variable `.var v`, `.bot`, `.top` or
`.node a` with `a : Fin n → Term n V`; `BFTerm n V` has no `.top`. A system
`TermSystem n V` is a list of constraints `.le e e'` and `.eq e e'`
(`BFTermSystem n V` over `{⊥, f}`), and `ExistsEntailsTerm c φ ψ` is
existential entailment for an antecedent over the visible variables `X` and a
consequent over `X ⊕ Z`; its variants are `ExistsEntailsTermReg`, `ExistsEntailsTermFin` and,
over `{⊥, f}`, `ExistsEntailsTermTopFree`, `ExistsEntailsTermTopFreeReg` and
`ExistsEntailsTermTopFreeFin`. The variable types are finite with decidable
equality:

```lean
-- [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
def decideExistsEntailsTerm (c : Fin n → Bool) (φ : TermSystem n X)
    (ψ : TermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTerm c φ ψ)
def decideExistsEntailsTermTopFree (φ : BFTermSystem n X)
    (ψ : BFTermSystem n (X ⊕ Z)) : Decidable (ExistsEntailsTermTopFree φ ψ)
```

and likewise `decideExistsEntailsTermReg`, `decideExistsEntailsTermFin`,
`decideExistsEntailsTermTopFreeReg` and `decideExistsEntailsTermTopFreeFin`.
They flatten both systems and run the core deciders of `Core.Main` on the
flat systems, over `{⊥, f}` after adding the top-freeness gadget.

A constrained type scheme `Scheme P T` has the constraints
`constraint : List (TermLit T)`, the context `context`, a finite map from the
program variables `P` to expressions, and the type `type : T`; the expressions
are `Term n (F ⊕ B)` over `{⊥, f, ⊤}` and `BFTerm n (F ⊕ B)` over `{⊥, f}`,
with free variables `F` and bound variables `B`. `Subsumes c S₁ S₂` holds when, under every valuation of the free
variables, every instance of `S₂` lies above some instance of `S₁`, contexts
being compared contravariantly; `SubsumesIn C c S₁ S₂` is the same with all
values in the tree class `C`. With `[DecidableEq P]` and finite `F`, `B₁`, `B₂`
with decidable equality,

```lean
def decideSubsumes (c : Fin n → Bool) (S₁ : Scheme P (Term n (F ⊕ B₁)))
    (S₂ : Scheme P (Term n (F ⊕ B₂))) : Decidable (Subsumes c S₁ S₂)
def decideSubsumesTopFree (S₁ : Scheme P (BFTerm n (F ⊕ B₁)))
    (S₂ : Scheme P (BFTerm n (F ⊕ B₂))) : Decidable (SubsumesTopFree S₁ S₂)
```

and likewise `decideSubsumesReg`, `decideSubsumesFin`,
`decideSubsumesTopFreeReg` and `decideSubsumesTopFreeFin`. They rest on the
subsumption formula `subsumesIn_iff`: if the context of `S₁` has a domain
contained in that of `S₂`, then `S₁ ≤ S₂` iff
`C₂ ⊨ ∃ ā₁. (C₁ ∧ τ₁ ≤ τ₂ ∧ ⋀_{v ∈ Dom Γ₁} Γ₂(v) ≤ Γ₁(v))`, with the free variables and the
bound variables of `S₂` visible; otherwise it holds iff `C₂` has no solution
(`subsumesIn_iff_of_not_subset`). The correctness theorems are named as above.

### Plain entailment

A conjunction `φ : Constraint n k` of deci-nsse embeds as `liftConstraint φ`
(literal by literal, `Lit.toELit`), and `query x y : EConstraint n (k + 0)` is
the literal `x ≤ y` with no hidden variables. The three reductions are

```lean
theorem nsse_iff_ensse {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k) (x y : V k) :
    Entails c φ x y ↔ ExistsEntails (h := 0) c (liftConstraint φ) (query x y)
theorem nsseReg_iff_ensseReg {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsReg c φ x y ↔ ExistsEntailsReg (h := 0) c (liftConstraint φ) (query x y)
theorem nsseFin_iff_ensseFin {n k : ℕ} (c : Fin n → Bool) (φ : Constraint n k)
    (x y : V k) :
    EntailsFin c φ x y ↔ ExistsEntailsFin (h := 0) c (liftConstraint φ) (query x y)
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

For a covariant constructor over trees without top, the query is `bfQuery x y`,
and `decideEntailsTopFree` and its two variants decide `EntailsTopFree φ x y`
and its regular and finite variants, through `topFree_nsse_iff_ensse` and its
two variants. [Plain.lean](DeciENSSE/Plain.lean) specializes the class
transfers: regular and arbitrary plain entailment agree
(`existsEntailsReg_query_iff`), and finite plain entailment holds iff the
antecedent has no finite solution or arbitrary plain entailment holds
(`existsEntailsFin_query_iff`).

### API map

| Decider | Semantics | Correctness theorem | Module |
| --- | --- | --- | --- |
| `decideExistsEntails` | `ExistsEntails c φ ψ` | `decideExistsEntails_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsReg` | `ExistsEntailsReg c φ ψ` | `decideExistsEntailsReg_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsFin` | `ExistsEntailsFin c φ ψ` | `decideExistsEntailsFin_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsTopFree` | `ExistsEntailsTopFree φ ψ` | `decideExistsEntailsTopFree_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsTopFreeReg` | `ExistsEntailsTopFreeReg φ ψ` | `decideExistsEntailsTopFreeReg_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsTopFreeFin` | `ExistsEntailsTopFreeFin φ ψ` | `decideExistsEntailsTopFreeFin_correct` | [Main](DeciENSSE/Main.lean) |
| `decideExistsEntailsTerm` | `ExistsEntailsTerm c φ ψ` | `decideExistsEntailsTerm_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideExistsEntailsTermReg` | `ExistsEntailsTermReg c φ ψ` | `decideExistsEntailsTermReg_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideExistsEntailsTermFin` | `ExistsEntailsTermFin c φ ψ` | `decideExistsEntailsTermFin_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideExistsEntailsTermTopFree` | `ExistsEntailsTermTopFree φ ψ` | `decideExistsEntailsTermTopFree_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideExistsEntailsTermTopFreeReg` | `ExistsEntailsTermTopFreeReg φ ψ` | `decideExistsEntailsTermTopFreeReg_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideExistsEntailsTermTopFreeFin` | `ExistsEntailsTermTopFreeFin φ ψ` | `decideExistsEntailsTermTopFreeFin_correct` | [Flattening](DeciENSSE/Flattening.lean) |
| `decideSubsumes` | `Subsumes c S₁ S₂` | `decideSubsumes_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideSubsumesReg` | `SubsumesReg c S₁ S₂` | `decideSubsumesReg_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideSubsumesFin` | `SubsumesFin c S₁ S₂` | `decideSubsumesFin_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideSubsumesTopFree` | `SubsumesTopFree S₁ S₂` | `decideSubsumesTopFree_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideSubsumesTopFreeReg` | `SubsumesTopFreeReg S₁ S₂` | `decideSubsumesTopFreeReg_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideSubsumesTopFreeFin` | `SubsumesTopFreeFin S₁ S₂` | `decideSubsumesTopFreeFin_correct` | [Subsumption](DeciENSSE/Subsumption.lean) |
| `decideEntails` | `DeciNSSE.Entails c φ x y` | `decideEntails_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsReg` | `DeciNSSE.EntailsReg c φ x y` | `decideEntailsReg_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsFin` | `DeciNSSE.EntailsFin c φ x y` | `decideEntailsFin_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFree` | `EntailsTopFree φ x y` | `decideEntailsTopFree_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFreeReg` | `EntailsTopFreeReg φ x y` | `decideEntailsTopFreeReg_correct` | [NSSE](DeciENSSE/NSSE.lean) |
| `decideEntailsTopFreeFin` | `EntailsTopFreeFin φ x y` | `decideEntailsTopFreeFin_correct` | [NSSE](DeciENSSE/NSSE.lean) |

The semantics of flat systems are defined in
[Semantics.lean](DeciENSSE/Semantics.lean), those of type expressions in
[Terms.lean](DeciENSSE/Terms.lean) and subsumption in
[Subsumption.lean](DeciENSSE/Subsumption.lean), except the plain
`DeciNSSE.Entails` and its variants, which are in
[Constraints/Basic.lean](DeciNSSE/Constraints/Basic.lean). Below this
interface, `Core.Main.decideExistsEntails` and its two variants decide the full
signature for variables in arbitrary finite types `X` and `X ⊕ Z`. The flat
deciders reach them through `toCoreFull`, `splitFull`, `existsEntails_iff_core`
and its variants, and over `{⊥, f}` through the gadget translation
`toCoreTopFree`, `splitTopFree`, `existsEntailsTopFree_iff_core` and its
variants. [Examples/Public](DeciENSSE/Examples/Public.lean) proves
`Examples.hiddenExtension`, `Examples.not_existsEntails_unconstrained_eqTop`,
the binary example and the class separation above, and evaluates the deciders
in the kernel at arity zero (`Examples.nullary_yes`, `Examples.nullary_no`).
[Examples/Subsumption](DeciENSSE/Examples/Subsumption.lean) proves the worked
examples on constrained arrow types of the paper. The other modules under
[Examples](DeciENSSE/Examples) exercise the library layers on small instances.

## Proof overview

The proof works with `{⊥, f, ⊤}` over arbitrary trees, reduces failures of the
entailment to holes of finite readers, bounds the length of a shortest hole,
and transfers the result to the other tree classes and to `{⊥, f}`; every step
is proved in Lean, along the route of the paper. The proof map in
[Main.lean](DeciENSSE/Main.lean) lists the theorems of each step, and the
modules under [Paper](DeciENSSE/Paper) state each numbered result of the paper.

1. **Arity zero.** The general deciders are correct at every arity, including
   zero. There the only trees are `⊥ < f() < ⊤`, and the arity dispatch
   [Core/Main](DeciENSSE/Core/Main.lean) uses instead the label enumeration of
   [Core/Nullary](DeciENSSE/Core/Nullary.lean), a search small enough for the
   kernel to evaluate.

2. **Leaf cones and three conditions.** A tree is described by two *leaf
   cones*: the words whose path meets a leaf of sign 0, and those whose path
   meets a leaf of sign 1, where the sign combines the label `⊥` or `⊤` with
   the polarity of the path. The order adds leaves of sign 0 and removes
   leaves of sign 1 (`Core.Mixed.treeLe_iff_leaf`), and every system becomes a
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

3. **Automata and self events.** The signed translation
   ([Full/Signed](DeciENSSE/Core/Full/Signed.lean)) gives each variable a
   positive and a negative copy; over these the moves form a pushdown system,
   summarized by an *upper* automaton for pops and a *lower* one for pushes
   ([Core/Automata](DeciENSSE/Core/Automata): Saturation, Powerset, Moves).
   Finite-state searches decide satisfiability and (I0). Variance adds a new
   way for an atom to be dead, a *self event*: a comparison of one word with
   its own suffixes whose automaton states are related (Mixed: Signed,
   SummaryFacts, Membership, Sat, CondI0).

4. **Holes for (U) and (II).** A *reader* is a finite automaton with rejected
   states and an admission relation on pairs of states; a *comparison* of `w`
   is a pair of cuts `s < e` with `w.drop e` a prefix of `w.drop s`; a *hole*
   is a rejected word without an admitted comparison. The failures of (U) are
   the holes of a *unit reader* that admits the self events, decided by
   `RejectedTail.decideHole` ([Units](DeciENSSE/Core/Mixed/Units.lean)). Under
   (U), (II) fails iff an extracted *two-word instance* with self events has a
   hole: a safe *spine* word and a *target* word with a rejected cut, a
   comparison of equal suffixes carrying a head pair, and no guarded cross
   comparison or self event up to the first rejected cut
   ([Extract](DeciENSSE/Core/Mixed/Extract.lean), `Core.Mixed.mixed_reduction`),
   and the closure of its seed is a countermodel
   ([ExtractModel](DeciENSSE/Core/Mixed/ExtractModel.lean)). Extracted
   instances have *forced target heads*, which the bounds below need.

5. **Holes that are not mortal.** After the first rejected cut of the target
   both words share a suffix, which keeps an event only by continuing it
   periodically. From a *branching* spine state a continuation breaking every
   such obligation exists by the Fine–Wilf theorem; from a *thin* one, long
   continuations follow finitely many lassos, and a pump shortens the purely
   periodic ones. These holes have length polynomial in the state counts
   (`Core.Words.Self.nonMortalShortHoleBoundSelf`). In the remaining *mortal*
   case the spine has no infinite safe continuation. The general word facts are
   in [Core/Words](DeciENSSE/Core/Words) (Streams, NonMortal, NonMortalLasso,
   Periodic, NonMortalBound, and the deletion toolkit Pump); the case analysis,
   the deletion and counting lemmas and the pump are in
   [Core/Words/Self](DeciENSSE/Core/Words/Self).

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
   short-hole theorem `Core.Words.Self.shortHoleBoundSelf` for every finite
   alphabet, and `Core.Mixed.decideExistsEntails` tests satisfiability, (I0)
   and (U) and then searches every extracted instance below that bound
   ([Mixed/Decide](DeciENSSE/Core/Mixed/Decide.lean),
   [Mixed/Final](DeciENSSE/Core/Mixed/Final.lean)).

7. **Regular and finite trees, by pinning and medians.** A failed extension of
   a solution of `φ` is retained by at most two visible observations
   (`Core.Mixed.two_observations_mixed`), each a finite ground bound
   ([Mixed/ClassTransfer](DeciENSSE/Core/Mixed/ClassTransfer.lean)). A
   satisfiable system with ground bounds has a regular solution, and graph
   equations pin visible regular values, so regular and arbitrary entailment
   coincide (`Core.Mixed.existsEntailsTReg_iff_mixed`). A system with a finite
   solution that is satisfiable with finitely many ground bounds has a finite
   solution satisfying them (`Core.Mixed.exists_finite_sat_groundBounds`):
   pass to signed variables, encode path pins by ranked chains of fresh
   variables, and restore sign symmetry by a median of three finite
   assignments. The median of three finite trees is finite, since beyond their
   depth the constant leaf extensions of all three carry extreme labels only
   (`Support.Median.finite_treeMedian`). Hence finite entailment holds iff `φ`
   has no finite solution, or `ψ` has one and arbitrary entailment holds
   (`Core.Mixed.existsEntailsTFin_iff_mixed`).

8. **The signature `{⊥, f}`.** For a covariant constructor the gadget
   `v ≤ y_v ∧ y_v ≤ f(y_v, …, y_v)`, with a fresh variable `y_v`, forces `v`
   to be top-free, and in each tree class every top-free tree has a witness:
   `Ω = f(Ω, …, Ω)` over arbitrary and regular trees, and the full finite tree
   `T_{h(t)+1}` over finite trees. Adding the gadget on every visible and every
   hidden variable reduces existential entailment over `{⊥, f}` to the full
   signature at the covariant variance, in the same tree class
   (`TopFree.existsEntailsTIn_iff_gadget`), so the three deciders for `{⊥, f}`
   are the full-signature deciders on the translated systems
   ([TopFree](DeciENSSE/TopFree.lean), [Main](DeciENSSE/Main.lean)).

9. **Type expressions and constrained types.** Flattening reduces systems of
   type expressions to flat systems in every tree class that contains the
   values of the subexpressions, at every variance and for both signatures
   (`Flattening.existsEntailsTermIn_iff_flatten`); over `{⊥, f}` the gadget is
   then placed on every variable of the flat systems, names included.
   Subsumption of constrained type schemes is an existential entailment
   between such systems (`subsumesIn_iff`, `subsumesIn_iff_of_not_subset`),
   hence decidable ([Flattening](DeciENSSE/Flattening.lean),
   [Subsumption](DeciENSSE/Subsumption.lean)).

10. **Counterexample words and countermodels.** A failure of entailment between
    satisfiable systems has a *counterexample word*: a word witnessing a
    failure of (I0), of (U), or the separator word of a hole of an extracted
    instance. Its length is bounded in the number `v` of visible and the
    number `s` of all variables, independently of the arity and the variance,
    and the word determines a countermodel by at most two observation pins, in
    each tree class ([Certificate](DeciENSSE/Certificate.lean),
    [Counterexamples](DeciENSSE/Counterexamples.lean),
    [Bounds](DeciENSSE/Bounds.lean)).

## Scope

**Decidability in principle.** The deciders are computable definitions with
compiled code that run finite searches justified by proved bounds; classical
reasoning enters the proofs of the bounds and of correctness, not the
searches. The bounds are far too large for practical type inference, the
examples evaluate the deciders only at arity zero, and the deciders return
only the answer, not a counterexample word or a countermodel.

**Bounds proved in Lean.** Every search bound is an explicit function of the
state counts of the automata involved, and these counts are functions of the
number of variables. For a two-word instance with spine, target and head
automata of `a`, `b`, `a'`, `b'` states:

- *Anchored compression* (`Anchored.exists_short_posHole_elementary`): a
  positive hole of depth at most `d` of a monitor with `N` cores has one of
  length at most `Anchored.anchoredLengthBound N d`, and
  `Anchored.anchoredLengthBound_le` proves, with `Ξ = Anchored.anchoredExponent N d`,

  ```text
  anchoredLengthBound N d ≤ 2^(2^(5 Ξ + 6)),   Ξ = 6N² + 10N(N + d)(d + 1) + 7N + 3d + 4.
  ```
- *Mortal holes* (`Core.Words.Self.exists_short_mortalHole`): some mortal hole
  has a separator word of length at most `Core.Words.Mortal.mortalHoleBound a b a' b'`,
  that is, `anchoredLengthBound N (2 N a - 1)` with `N = 1 + a a' + b b' + a b'`.
  If `N ≤ 2^α` with `α ≥ 3` and `a ≤ 2^β`, it is at most `E₃(3α + 2β + 9)`
  (`Bounds.mortalHoleBound_le_E3`), where `E₃(x) = 2^(2^(2^x))` (`Bounds.E3`).
- *Holes that are not mortal* (`Core.Words.Self.nonMortalShortHoleBoundSelf`):
  `Core.Words.pumpHoleBound a b a' b' = 4 max(12 a b a' b', P) + 6 a`, where
  `P = Core.Words.pumpCapacity a b a' b' = 2 a b a' b' + a² a' + a b + a a' + b b'`
  is a polynomial of degree 4; for positive state counts the bound is at most
  `54 a² b a' b'` (`Bounds.pumpHoleBound_le`).
- *All holes* (`Core.Words.Self.shortHoleBoundSelf`): the maximum of the two,
  `Core.Words.Self.selfHoleBound`.
- *Condition (U)*: `DeciNSSE.RejectedTail.holeLengthBound N`, at most
  `2^(2^(1280 (N + 1)^5))` for a reader with `N` states
  (`DeciNSSE.RejectedTail.holeLengthBound_le`), and at most `E₃(5k + 12)` for
  `N = 2^k ≥ 8` (`Bounds.holeLengthBound_two_pow_le`).
- *Counterexample words* (`exists_short_counterexampleWord`): with `v` visible
  and `s` variables in all, both systems satisfiable in the tree class and the
  entailment failing there, some counterexample word has length at most
  `E₃(10v + 12s + 15) ≤ E₃(22s + 15)`. Over `{⊥, f}` the gadget doubles the
  variables, and the gadget pair has one of length at most
  `E₃(20v + 24s + 15) ≤ E₃(44s + 15)` (`exists_short_counterexampleWord_gadget`).
  [Bounds/States](DeciENSSE/Bounds/States.lean) counts the states of every
  reader of the procedure in terms of `v` and `s`.

**Not mechanized.** The section *Complexity and Sharper Bounds* of the paper
and its appendix are not formalized here: the smaller reader for (U) with its
sharper bound, the 2-EXPSPACE and 3-EXPTIME upper bound by a search over
compression summaries, membership in PSPACE for `n ≤ 1`, the exponential lower
bound on shortest counterexamples, and PSPACE-hardness for every fixed arity
`n ≥ 2`. The theorem covers one constructor; several constructors, entailment
of disjunctions and `{⊥, f}` with a contravariant argument are not covered.

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
python3 scripts/contract.py --strict --axioms
```

The package pins Lean and Mathlib to **v4.35.0**. The first command downloads
compiled Mathlib dependencies; the second checks both libraries, `DeciNSSE`
and `DeciENSSE`. There are no executables. The third command, run after the
build, checks the correspondence between the paper and the contract modules
under `DeciENSSE/Paper`, that every contract declaration uses only the axioms
below, and that every decision procedure among them compiles to executable
code ([scripts/README-contract.md](scripts/README-contract.md)); it needs
Python 3 and no further packages.

To inspect the logical dependencies of the public theorems, save the following
as `Check.lean` and run `lake env lean Check.lean`:

```lean
import DeciENSSE

#print axioms DeciENSSE.decideExistsEntails_correct
#print axioms DeciENSSE.decideExistsEntailsReg_correct
#print axioms DeciENSSE.decideExistsEntailsFin_correct
#print axioms DeciENSSE.decideExistsEntailsTopFree_correct
#print axioms DeciENSSE.decideExistsEntailsTopFreeReg_correct
#print axioms DeciENSSE.decideExistsEntailsTopFreeFin_correct
#print axioms DeciENSSE.decideExistsEntailsTerm_correct
#print axioms DeciENSSE.decideExistsEntailsTermReg_correct
#print axioms DeciENSSE.decideExistsEntailsTermFin_correct
#print axioms DeciENSSE.decideExistsEntailsTermTopFree_correct
#print axioms DeciENSSE.decideExistsEntailsTermTopFreeReg_correct
#print axioms DeciENSSE.decideExistsEntailsTermTopFreeFin_correct
#print axioms DeciENSSE.decideSubsumes_correct
#print axioms DeciENSSE.decideSubsumesReg_correct
#print axioms DeciENSSE.decideSubsumesFin_correct
#print axioms DeciENSSE.decideSubsumesTopFree_correct
#print axioms DeciENSSE.decideSubsumesTopFreeReg_correct
#print axioms DeciENSSE.decideSubsumesTopFreeFin_correct
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
proof 110 files under `DeciENSSE/`, with 11,687 and 28,000 lines including the
root modules `DeciNSSE.lean` and `DeciENSSE.lean`, through which every module
of each library is imported. The counts include comments and docstrings; the 9
example modules under `DeciENSSE/Examples/` account for 4,636 of the lines and
the 15 contract modules `DeciENSSE/Paper.lean` and `DeciENSSE/Paper/` for
3,232. Namespaces are relative to `DeciNSSE` or `DeciENSSE`; "top level" means
the root namespace itself. The folder [paper](paper) holds the LaTeX sources of
the write-up and the compiled [main.pdf](paper/main.pdf); build it with `make`
in that folder. The folder [scripts](scripts) holds the contract checker.

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
| [Semantics](DeciENSSE/Semantics.lean) | top level | Public syntax, the six existential semantics, plain entailment as a query |
| [Main](DeciENSSE/Main.lean) | top level | Conversions to the core, the six existential deciders, the proof map |
| [NSSE](DeciENSSE/NSSE.lean), [Plain](DeciENSSE/Plain.lean) | top level | Plain entailment: reductions, NSSE deciders and the top-free variants; regular and finite plain entailment |
| [Terms](DeciENSSE/Terms.lean), [Flattening](DeciENSSE/Flattening.lean) | top level, `Term`, `BFTerm`, `TermLit`, `Flattening` | Type expressions and constraints between them, flattening and its size, the six deciders for systems of expressions |
| [Subsumption](DeciENSSE/Subsumption.lean) | top level, `Scheme` | Constrained type schemes and their instances, the subsumption formula, the six subsumption deciders |
| [TopFree](DeciENSSE/TopFree.lean) | `TopFree`, `DeciNSSE.FTree` | Top-free trees, the gadget and its witnesses, the reduction of `{⊥, f}` to `{⊥, f, ⊤}` |
| [Certificate](DeciENSSE/Certificate.lean), [Counterexamples](DeciENSSE/Counterexamples.lean) | top level, `CounterexampleWord`, `CertificateTreeClass`, `TopFree` | Counterexample words and their countermodels, short counterexample words in each tree class |
| [Bounds](DeciENSSE/Bounds.lean) and [Bounds/](DeciENSSE/Bounds): States, Estimates, Tower | `Bounds` | State counts of the readers, closed forms of the bounds, the triple exponential `E₃`, counterexample bounds in the number of variables |
| [Paper](DeciENSSE/Paper.lean) and [Paper/](DeciENSSE/Paper): Introduction, Background, Flattening, Leaf, Characterization, Summaries, Units, Extraction, NonMortal, Mortal, Bounds, Classes, Assembly, Applications | `Paper` | The contract: one declaration per numbered result, or numbered item, of the paper, named after its label |
| [Core/Main](DeciENSSE/Core/Main.lean), [Core/Nullary](DeciENSSE/Core/Nullary.lean), [Support/Nullary](DeciENSSE/Support/Nullary.lean) | `Core.Main`, `Core.Nullary`, `Support.Nullary` | Deciders over finite carriers, the arity dispatch, label enumeration at arity zero |
| [Core/Basic](DeciENSSE/Core/Basic.lean) | `Core`, `Core.PrefixSet` | Prefix-closed sets of words, covariant pushdown rules and their moves |
| [Core/Automata](DeciENSSE/Core/Automata): Saturation, Powerset, Moves | `Core.Automata` | Saturation, upper and lower powerset automata, move paths and their lowest point |
| [Core/Full](DeciENSSE/Core/Full): Basic, Signed | `Core.Full` | Full-signature syntax over arbitrary carriers, the signed translation |
| [Core/Full](DeciENSSE/Core/Full): AC, Observations, ACPins, Classes, TopGraphs | `Core.Full`, `Core.Full.AC`, `Core.Full.ACPins`, `Core.Full.TopGraphs` | Observations and ground bounds, the restricted tree classes, graph equations for regular trees |
| [Core/Full](DeciENSSE/Core/Full): Flatten, Pinning, PinningGround, PinningSpines | `Core.Full`, `Core.Full.Flatten`, `Core.Full.Pinning` | Elimination of variable inequalities by constructor sandwiches, finite satisfiability, covariant finite-bound pinning |
| [Core/Mixed](DeciENSSE/Core/Mixed): Leaf, LeafHorn, Duality, Conditions | `Core.Mixed` | Leaf cones, the Horn presentation, duality and deadness, the three conditions |
| [Core/Mixed](DeciENSSE/Core/Mixed): Signed, SummaryFacts, Membership, Sat, CondI0, Units | `Core.Mixed` | Leaf-move automata, roots and sign coherence of summaries, self events, satisfiability, conditions (I0) and (U) |
| [Core/Mixed](DeciENSSE/Core/Mixed): Extract, ExtractModel, Decide, Final | `Core.Mixed`, `Core.Words.Self.SelfTwoWordInstance` | Two-word instances with self events, countermodels from their holes, bounded search, the arbitrary-tree decider |
| [Core/Mixed](DeciENSSE/Core/Mixed): ClassTransfer, Regular, Finite, FinitePinningSigned, FinitePinning | `Core.Mixed`, `Core.Mixed.FinitePinning` | Two observations and class transfer, regular and finite trees, finite-bound pinning by medians |
| [Support](DeciENSSE/Support): Graphs, Median, Spines, RankedExtension | `Support.Graphs`, `Support.Median`, `Support.Spines`, `Support.RankedExtension` | Graph unfoldings and regular satisfiability, tree medians and finite medians, path pins as constraint chains, ranked extensions |
| [Support](DeciENSSE/Support): Normalization, HoleCorrespondence | `Support`, `Support.HoleCorrespondence` | Normalization and duality beyond the shared library; hierarchy, core, exchange-type and column facts of the shared library in the form of the paper |
| [Core/Words](DeciENSSE/Core/Words): LDFA, Streams, TwoWordInstance, Transport | `Core.Words`, `Core.Words.LDFA`, `Core.Words.TwoWordInstance` | Automata over arbitrary alphabets, infinite words and periods, two-word hole instances, renaming |
| [Core/Words](DeciENSSE/Core/Words): NonMortal, NonMortalLasso, Periodic, NonMortalBound, Pump | `Core.Words`, `Core.Words.TwoWordInstance`, `Core.Words.TwoTapeGraph`, `Core.Words.PeriodicSplit` | Safe paths and their cases, lassos, periodic splits, the finite pre-hole search, the deletion toolkit and the non-mortal bound |
| [Core/Words/Mortal](DeciENSSE/Core/Words/Mortal): SepWord, PiReader, Depth, Bound | `Core.Words.Mortal` | Separator words, the Π-reader, the depth of mortal holes, the mortal bound |
| [Core/Words/Self](DeciENSSE/Core/Words/Self): Basic, NonMortal, Pump, PaperFacts, Mortal, Bound | `Core.Words.Self`, `Core.Words.Self.SelfTwoWordInstance` | Instances with self events, the case analysis, the pump, the deletion and counting lemmas, mortal compression, the short-hole theorem |
| [Anchored](DeciENSSE/Anchored): Channel, Desubstitution, Agree, Columns, Unary, NormalForm, Types, ElementaryBound, Estimate, Monotone | `Anchored` | Positive channels, anchored compression, the number of anchored exchange types, the elementary bound, its closed form and monotonicity |
| [Examples](DeciENSSE/Examples): Public, FiniteTests, ShiftClosure, Subsumption, Words, Self, Full, Mixed, Fixtures | `Examples`, and `…Examples` namespaces beside the code they exercise | Small proved and evaluated instances and their shared fixtures; apart from the root module and the contract modules, which import ShiftClosure and Subsumption, the examples of the paper, no library module imports an example module |

## License

Apache License 2.0; see [LICENSE](LICENSE).
