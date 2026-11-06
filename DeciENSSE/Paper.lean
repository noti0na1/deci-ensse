import DeciENSSE.Paper.Classes
import DeciENSSE.Paper.Background
import DeciENSSE.Paper.Leaf
import DeciENSSE.Paper.Characterization
import DeciENSSE.Paper.Summaries
import DeciENSSE.Paper.Units
import DeciENSSE.Paper.Extraction
import DeciENSSE.Paper.NonMortal
import DeciENSSE.Paper.Mortal
import DeciENSSE.Paper.Flattening
import DeciENSSE.Paper.Bounds
import DeciENSSE.Paper.Assembly
import DeciENSSE.Paper.Applications
import DeciENSSE.Paper.Introduction

/-! # The paper–Lean contract

One module per section of the paper states the numbered results of that section and of its
appendix, as declarations in the namespace `DeciENSSE.Paper` named after the paper labels:
item (3) of `lem:tc-median` is `DeciENSSE.Paper.lem_tc_median_3`. The first docstring line of
each declaration names the result, and an optional `Form:` line records how the statement
is represented in Lean. The script `scripts/contract.py` checks these declarations against
the LaTeX sources and generates the correspondence table of the paper's appendix; the format
and the checks are described in `scripts/README-contract.md`.
-/
