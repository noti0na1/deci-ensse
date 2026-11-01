import DeciNSSE.Constraints.Basic
import DeciNSSE.Constraints.Closure
import DeciNSSE.Constraints.Dual
import DeciNSSE.Constraints.PathBounds
import DeciNSSE.Constraints.Signed
import DeciNSSE.Holes.Agree
import DeciNSSE.Holes.Basic
import DeciNSSE.Holes.BoundaryPairs
import DeciNSSE.Holes.BoundedDepth
import DeciNSSE.Holes.CoAlignment
import DeciNSSE.Holes.Columns
import DeciNSSE.Holes.CoreOccurrences
import DeciNSSE.Holes.Cores
import DeciNSSE.Holes.Depth
import DeciNSSE.Holes.Desubstitution
import DeciNSSE.Holes.ElementaryBound
import DeciNSSE.Holes.Exchange
import DeciNSSE.Holes.Hierarchy
import DeciNSSE.Holes.Hierarchy.Canonical
import DeciNSSE.Holes.Hierarchy.Derived
import DeciNSSE.Holes.Hierarchy.Expansion
import DeciNSSE.Holes.Hierarchy.Reader
import DeciNSSE.Holes.Hierarchy.Starts
import DeciNSSE.Holes.Hierarchy.Unary
import DeciNSSE.Holes.LevelMaps
import DeciNSSE.Holes.NormalForm
import DeciNSSE.Holes.Packets
import DeciNSSE.Holes.StartCores
import DeciNSSE.Holes.Supports
import DeciNSSE.RejectedTail.Basic
import DeciNSSE.RejectedTail.BoundedTail
import DeciNSSE.RejectedTail.Decision
import DeciNSSE.RejectedTail.Depth
import DeciNSSE.RejectedTail.DepthCount
import DeciNSSE.RejectedTail.Forced
import DeciNSSE.RejectedTail.Periodic
import DeciNSSE.RejectedTail.ReturnGap
import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Satisfiability.Decide
import DeciNSSE.Satisfiability.Finite
import DeciNSSE.Satisfiability.FiniteVariance
import DeciNSSE.Satisfiability.LeastShape
import DeciNSSE.Satisfiability.ShapeGraph
import DeciNSSE.Semantics.Characterization
import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Normalization
import DeciNSSE.Semantics.Order
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Safety
import DeciNSSE.Semantics.Selector
import DeciNSSE.Semantics.Sym
import DeciNSSE.Semantics.Tree
import DeciNSSE.Transfer.RankedExtension
import DeciNSSE.Words

/-! # Shared library for non-structural subtype entailment

Tree semantics, flat constraints, satisfiability, readers, holes, the
canonical block hierarchy, the elementary hole-length bound and the
rejected-tail decision for one constructor of arbitrary finite arity and
variance, over arbitrary, regular and finite trees. The existential
entailment proof in `DeciENSSE` builds on these modules.
-/
