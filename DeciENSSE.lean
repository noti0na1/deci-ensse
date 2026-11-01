import DeciENSSE.Anchored.Agree
import DeciENSSE.Anchored.Channel
import DeciENSSE.Anchored.Columns
import DeciENSSE.Anchored.Desubstitution
import DeciENSSE.Anchored.ElementaryBound
import DeciENSSE.Anchored.Estimate
import DeciENSSE.Anchored.NormalForm
import DeciENSSE.Anchored.Unary
import DeciENSSE.Core.Automata
import DeciENSSE.Core.AutomataDecide
import DeciENSSE.Core.Basic
import DeciENSSE.Core.Classes
import DeciENSSE.Core.ClassesLanguage
import DeciENSSE.Core.Decide
import DeciENSSE.Core.Final
import DeciENSSE.Core.Full.AC
import DeciENSSE.Core.Full.ACPins
import DeciENSSE.Core.Full.Basic
import DeciENSSE.Core.Full.Bridge
import DeciENSSE.Core.Full.Classes
import DeciENSSE.Core.Full.Flatten
import DeciENSSE.Core.Full.Observations
import DeciENSSE.Core.Full.Pinning
import DeciENSSE.Core.Full.PinningGround
import DeciENSSE.Core.Full.PinningSpines
import DeciENSSE.Core.Full.TopGraphs
import DeciENSSE.Core.Horn
import DeciENSSE.Core.Main
import DeciENSSE.Core.Mixed.CondI
import DeciENSSE.Core.Mixed.Conditions
import DeciENSSE.Core.Mixed.Decide
import DeciENSSE.Core.Mixed.Duality
import DeciENSSE.Core.Mixed.Extract
import DeciENSSE.Core.Mixed.Final
import DeciENSSE.Core.Mixed.Finite
import DeciENSSE.Core.Mixed.FinitePinning
import DeciENSSE.Core.Mixed.FinitePinningSigned
import DeciENSSE.Core.Mixed.Leaf
import DeciENSSE.Core.Mixed.LeafHorn
import DeciENSSE.Core.Mixed.Membership
import DeciENSSE.Core.Mixed.Regular
import DeciENSSE.Core.Mixed.Sat
import DeciENSSE.Core.Mixed.Signed
import DeciENSSE.Core.Mixed.Units
import DeciENSSE.Core.Nullary
import DeciENSSE.Core.Reduction
import DeciENSSE.Core.Words.Bound
import DeciENSSE.Core.Words.LDFA
import DeciENSSE.Core.Words.Mortal.Bound
import DeciENSSE.Core.Words.Mortal.Depth
import DeciENSSE.Core.Words.Mortal.PiReader
import DeciENSSE.Core.Words.Mortal.SepWord
import DeciENSSE.Core.Words.NonMortal
import DeciENSSE.Core.Words.NonMortalBound
import DeciENSSE.Core.Words.NonMortalLasso
import DeciENSSE.Core.Words.Periodic
import DeciENSSE.Core.Words.Pump
import DeciENSSE.Core.Words.SS2
import DeciENSSE.Core.Words.Self.BoundS
import DeciENSSE.Core.Words.Self.MortalS
import DeciENSSE.Core.Words.Self.NonMortalS
import DeciENSSE.Core.Words.Self.PumpS
import DeciENSSE.Core.Words.Self.SS2Self
import DeciENSSE.Core.Words.Statements
import DeciENSSE.Core.Words.Transport
import DeciENSSE.Examples
import DeciENSSE.Main
import DeciENSSE.NSSE
import DeciENSSE.Semantics
import DeciENSSE.Support.Nullary.Decide
import DeciENSSE.Support.Semantics.Regular
import DeciENSSE.Support.Transfer.RankedExtension
import DeciENSSE.Support.Transfer.Spines
import DeciENSSE.Support.TransferFin.CycleTransfer
import DeciENSSE.Support.TransferFin.FiniteMedian
import DeciENSSE.Support.Variance.Median
import DeciENSSE.Support.VarianceReg.RegularSat

/-! # Existential non-structural subtype entailment

Decision procedures for existential entailment `φ ⊨ ∃ z̄. ψ` between finite
conjunctions of subtype constraints over one constructor of arbitrary finite
arity, over arbitrary, regular and finite trees: for bottom, the constructor
and top with any variance, and for bottom and a covariant constructor. Plain
subtype entailment `φ ⊨ x ≤ y` follows as the instance with no hidden
variables (`DeciENSSE.NSSE`).
-/
