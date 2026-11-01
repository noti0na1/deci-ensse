import DeciENSSE.Core.Automata

/-! # Covariant constructor-set examples

The binary example extends a visible solution by choosing the hidden tree to
be the first visible tree. The nullary examples evaluate satisfiability tests
at the empty alphabet, where a constructor root still differs from bottom.
These exercise the semantics and finite saturation used in the covariant proof.

## Main declarations

- `CovariantExamples.binary_extension`: a hidden witness between visible bounds.
- `CovariantExamples.nullary_constructor_sat`: a nullary constructor has a model.
- `CovariantExamples.nullary_clash_unsat`: a forced root conflicts with bottom.
-/

namespace DeciENSSE.Core.CovariantExamples

/-- If `x ≤ y` and `x ≤ f(x, x)`, choose `z = x` for
`x ≤ z ∧ z ≤ y ∧ z ≤ f(z, z)`. -/
theorem binary_extension :
    ExistsEntailsTopFree
      ([.le false true, .lef false (fun _ => false)] : List (Lit 2 Bool))
      ([.le (.inl false) (.inr ()), .le (.inr ()) (.inl true),
        .lef (.inr ()) (fun _ => .inr ())] : List (Lit 2 (Bool ⊕ Unit))) := by
  intro ρ _ hρ
  have hxy : ρ false ≤ ρ true := hρ (.le false true) (by simp)
  have hxf : ρ false ≤ BFTree.node (fun _ => ρ false) :=
    hρ (.lef false (fun _ => false)) (by simp)
  refine ⟨fun _ => ρ false, fun _ => trivial, ?_⟩
  simpa [Sat, Lit.Holds, Function.comp_def] using
    And.intro (le_refl (ρ false)) (And.intro hxy hxf)

/-- With no children, the constructor lower bound forces only the root. -/
theorem nullary_constructor_sat :
    @decide (∃ ρ, Sat ρ ([.fle Fin.elim0 ()] : List (Lit 0 Unit)))
      (Automata.decideSat _) = true := by
  decide +kernel

/-- Even at arity zero, a constructor lower bound is incompatible with bottom. -/
theorem nullary_clash_unsat :
    @decide (∃ ρ, Sat ρ ([.fle Fin.elim0 (), .bot ()] : List (Lit 0 Unit)))
      (Automata.decideSat _) = false := by
  decide +kernel

end DeciENSSE.Core.CovariantExamples
