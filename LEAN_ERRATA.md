# Lean formalization errata and differences

This file records differences between the Lean development and Vlado Vojdanovski's *Rationality of the Moduli Space of Curves of Genus Nine*. The accompanying paper PDF is unchanged. The items below concern the formalization's scope and implementation; they are not assertions that the paper contains mathematical errors.

## 1. Page 1, Theorem 1.1: global variety structure

**Paper:** the variety M₉ is rational over ℂ, equivalently ℂ(M₉) ≅ ℂ(t₁,…,t₂₄).

**Lean:** the closed theorem `M9Native.M9PaperResult.paper_goal` proves `M9StandaloneDraft.RationalCoarseSpaceGoal ℂ`. It constructs the genuine coarse algebraic space for smooth, connected, unpointed genus-nine curves, with categorical universality against all algebraic-space targets and geometric classification over all algebraically closed complex extensions. It proves reducedness, separatedness, finite type and a common nonempty dense open with affine 24-space. The same chosen coarse space's structural complex function field is identified with ℂ(t₁,…,t₂₄).

**Omission:** the development does not separately establish global scheme representability of the entire coarse space. The stronger `RationalCoarseSchemeGoal` is not asserted. The formalization therefore proves the paper's equivalent function-field rationality conclusion while leaving this separate global structure assertion outside its proved statement.

Sources: [statement definitions](M9StacksIntegration/StandaloneModuliDraft.lean), [closed theorem and field package](M9StacksIntegration/M9PaperResult.lean).

## 2. Page 3, Proposition 2.2: associated-bundle argument

**Paper:** the radical map over the open orbit is described by the associated bundle G ×ᴴ Y; invariant functions are restricted to its fibre.

**Lean replacement:** explicit orbit-family function-field embeddings and characteristic-zero field descent establish the invariant-field identification. A separate global associated-bundle identification is not claimed as a formalized theorem at this step.

Sources: [radical invariant descent](M9StacksIntegration/PrimitiveRadicalInvariantDescent.lean), [fixed-field comparison](M9StacksIntegration/PrimitiveRadicalFixedFieldComparison.lean).

## 3. Page 4, Proposition 3.1: relative μ₃ quotient

**Paper:** a coordinate-ring calculation establishes the relative μ₃ quotient using X = dZ and d³ det(Z) = 1.

**Lean replacement:** the generic matrix field, its scalar μ₃ action, the degree-three fixed-field extension and determinant reconstruction prove the corresponding generic fixed-field identity. This retains the determinant twist but does not separately formalize the full relative quotient-scheme assertion.

Source: [determinant-twist field calculation](M9/DeterminantTwistField.lean), particularly `fixedField_eq_twistedEntryField` and `quotientCoordinateEquiv`.

## 4. Pages 6–7, Proposition 5.1: bundle descent

**Paper:** equivariant bundles descend to four-dimensional vector spaces over the quotient field; paired bases give the inversion action.

**Lean replacement:** explicit semilinear fixed-vector descent, paired bases and matrix function fields implement the needed generic-fibre argument. The inversion action, Cayley transformation and sixteen independent variables are retained. This is a reorganized proof of the field statement rather than a literal transcription of the global bundle presentation.

Source: [frame-bundle descent](M9/FrameBundleDescent.lean).

## 5. Page 7, Proposition 6.1: the no-name lemma

**Paper:** the cited no-name lemma is applied to the two projections of the single product ℙ(V₀) × P₀.

**Lean replacement:** explicit finite-Galois descent, denominator norms and the two product-field identifications establish the required conclusion. Domokos's general no-name theorem is not itself claimed as formalized. Both projections, the eight-variable stable-rationality conclusion and the final sixteen-variable extension remain in the argument.

Sources: [finite-Galois descent](M9/FiniteGaloisDescent.lean), [finite no-name calculation](M9/FiniteNoNameField.lean), [projective product-field comparisons](M9/ProjectiveNoName.lean), especially `firstProjectionEightEquiv`, `secondProjectionRationalEquiv` and `stableProjectiveInvariantEquiv`.

## 6. Meaning of a complete formalization

The proved endpoint is the unconditional rational coarse-algebraic-space and structural function-field result described in item 1. It should not be described as a verbatim formalization of every global geometric construction or every intermediate assertion in the paper.

The main strategy is retained: radical reduction, determinant twist, Cayley transformation, the S₄ wreath-product invariant calculation and the final 16 = 8 + 8 variable assembly. The development also supplies explicit coarse-moduli, Mukai, nonpentagonality and density bridges beyond the short arguments and citations in the paper. General foundations are reused from the pinned Mathlib and AxiomMath/Stacks libraries, with provenance recorded in [formalization.yaml](formalization.yaml) and [NOTICE.md](NOTICE.md).
