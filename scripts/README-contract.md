# Paper–Lean contract

Every theorem, lemma, proposition and corollary of the paper outside its complexity section
has a Lean declaration, a *contract entry*, in the modules `DeciENSSE/Paper/*.lean`, one
module per section of the paper; definitions and examples may have entries too. The script
`scripts/contract.py` (Python 3, standard library only) reads the LaTeX sources in
`paper/sections/` and these modules, checks that the two sides correspond, checks the axioms
and the executable code of the entries in the built library, and generates the
correspondence table of the paper's appendix.

## Commands

Run from the repository root (the script also finds the sources when it is invoked from
another directory):

```sh
python3 scripts/contract.py                  # report coverage
python3 scripts/contract.py --strict         # also fail on missing entries
python3 scripts/contract.py --table paper/sections/lean-table.tex
lake build
python3 scripts/contract.py --strict --axioms
```

The first two commands only read source files, and `--table` writes the rows of the table.
`--axioms` checks the compiled modules, so it runs after `lake build`; the script never
builds or updates packages. It writes a temporary Lean file outside the source tree, runs
`lake env lean` on it and removes it afterwards. To run that Lean process through a wrapper
script, for example one that serializes `lake` invocations, set the environment variable
`LAKE_LOCK` to the path of the script; it is then run as `zsh "$LAKE_LOCK" env lean <file>`.
The exit code is nonzero when a check fails.

## Entries

An entry is a public `theorem`, `lemma`, `def` or `abbrev` in the namespace
`DeciENSSE.Paper`. Its name is the paper label with every character other than a letter, a
digit or `_` replaced by `_`, followed by `_i` for item `i` of a result with numbered items:
item (3) of `lem:tc-median` is `DeciENSSE.Paper.lem_tc_median_3`. Its docstring begins with
the line

```text
**Lemma (Median)**, `lem:tc-median`(3).
```

that is, the kind (`Theorem`, `Lemma`, `Proposition`, `Corollary`, `Definition` or
`Example`), the title of the result, the label and the item number, if any. The docstring may
contain one further line beginning with `Form: `, in plain text, which records how the Lean
statement represents the statement of the paper; it becomes the last column of the table.

- A result without numbered items has one entry; a result with numbered items has one entry
  per item. Claims of a multipart result outside its items go into the statement of a
  suitable item, and its `Form:` line says so.
- Every theorem, lemma or definition of a contract module is an entry, and every docstring
  there belongs to an entry.
- Declarations and `namespace`, `section` and `end` commands start on their own lines;
  attributes stand on the lines before a declaration.
- A new contract module is imported in `DeciENSSE/Paper.lean`.

## Which results need an entry

The script reads every file in `paper/sections/` except `complexity.tex` and
`appendix-complexity.tex`, which are not mechanized, and `mechanization.tex` and
`appendix-lean.tex`, which describe the mechanization (the list is in `contract.py`).

- Every `theorem`, `lemma`, `proposition` and `corollary` environment needs a label and
  entries, unless its label begins with `rem:`.
- Labeled `definition` and `example` environments may have entries; unlabeled ones are
  ignored. Remarks never need entries.
- The items of a result are the `\item`s of an `enumerate` list directly inside the
  environment. Nested lists and equation labels do not count.
- An environment with several labels is recorded under each of them, with the same items.

## Decidability is a computable definition

In Lean's classical logic `Nonempty (Decidable P)` holds for every `P`, so a theorem of that
form says nothing. When the paper says that something is decidable, computable or can be
decided, the entry is a `def` (or `abbrev`), not marked `noncomputable`, whose value is the
decision procedure: a `Decidable`, `DecidablePred` or `DecidableRel` built from the
executable procedures of the library (for example `Core.Mixed.decideSatFin`, `decideCondU`
or `Self.decideHasMortalHole`). When the result says more, the value is a `PProd` (`×'`) of
the procedures and a proof of the remaining claims, as in
`def lem_x … : Decidable P ×' Q := ⟨d, h⟩`. A conditional claim ("if A is decidable, then so
is B") is a computable transformer `(∀ x, Decidable (A x)) → ∀ y, Decidable (B y)`.
Hypotheses such as the satisfiability of the antecedent become ordinary arguments.

Lean's compiler rejects a definition without `noncomputable` whose computational content
uses `Classical.choice`, `Classical.propDecidable` or `Classical.dec`, also through
`open Classical` or the `classical` tactic, so building the library checks that each
procedure is executable. Proofs inside the value may still be classical. The checker
rejects

- an entry declared `noncomputable`, `unsafe` or `partial`, or inside a
  `noncomputable section`;
- an entry whose statement, the text before its top-level `:=`, contains
  `Nonempty (Decidable`, `Nonempty (DecidablePred`, `Nonempty (DecidableRel` or
  `Nonempty (DecidableEq`, also when written with `<|` or `$`.

## The checks

Every run fails on

- an entry whose label, item number or kind does not exist in the paper, or whose name does
  not match its label and item;
- two entries for the same result or item;
- a declaration without a valid first docstring line, a docstring without a declaration, or
  more than one `Form:` line;
- an entry that is not public or that breaks the two rules of the previous section;
- an unlabeled theorem, lemma, proposition or corollary, a repeated label, nested result
  environments, unbalanced environments and unterminated Lean comments.

Missing required entries are listed by section file; they fail the run only with
`--strict`. With `--axioms`, the script imports every contract module and checks that
`#print axioms` reports, for every entry, only `propext`, `Classical.choice` and
`Quot.sound`. It also compiles, without evaluating it, one definition `@E` for every `def` or
`abbrev` entry `E`, which fails when `E` has no executable code. A Lean error or a missing
axiom report fails the run.

The script is a source-format checker, not a TeX macro expander or a Lean elaborator. It
handles balanced environments, TeX comments, nested Lean comments and Lean strings. A
passing run establishes that the numbered results and the entries correspond by label, item
and kind, and that the entries are kernel-checked declarations using only the three axioms,
with executable code for the decision procedures. It does not establish that a Lean statement
says what the statement of the paper says, or that the proof of an entry only applies
library results; this has to be checked by reading the statements.

## The table

`--table` writes the rows of a three-column `longtable`: the result and item, the fully
qualified declaration in `\lean{...}` (defined in `paper/macros.tex`), and the `Form:` note,
escaped for LaTeX. The rows follow the order of the section files and, within a file, the
order of the results and items. The output is deterministic, contains only existing entries
and is written even when entries are missing. The appendix `paper/sections/appendix-lean.tex`
includes the rows with `\input{sections/lean-table}`.
