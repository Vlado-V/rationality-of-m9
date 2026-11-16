module

public import M9StacksIntegration.AffineSpaceFunctionField
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.FunctionField

/-!
# The original affine space as a native variety

The underlying scheme and structure map are the literal original affine
space and its literal projection. The native variety function-field
scalar map agrees with the original structural scalar map. The actual
rational-function equivalence is then expressed with that native algebra
structure, retaining the same genuine generic-stalk carrier.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.AffineSpaceVariety

variable (K : Type u) [Field K] (n : ℕ)

/-- The native category object has the original affine-space scheme and projection. -/
def variety : Variety K where
  toScheme := AffineSpaceFunctionField.space K n
  structureMap := AffineSpaceFunctionField.projection K n
  isVariety := AffineSpaceFunctionField.isVariety K n

theorem variety_toScheme :
    (variety K n).toScheme = AffineSpace (ULift.{u} (Fin n)) (Spec (.of K)) := rfl

theorem variety_structureMap :
    (variety K n).structureMap = AffineSpaceFunctionField.projection K n := rfl

/-- The native generic-stalk scalar map is the actual original projection scalar map. -/
theorem nativeScalarMap_eq :
    functionFieldAlgebraMap (variety K n) =
      GrassmannianCharts.structureScalarMap K (AffineSpaceFunctionField.projection K n) := by
  rw [functionFieldAlgebraMap_eq_germToFunctionField]
  rfl

/-- The native algebra structure agrees with the one derived from the original projection. -/
theorem nativeAlgebra_eq :
    varietyFunctionFieldAlgebra (variety K n) = AffineSpaceFunctionField.functionFieldAlgebra K n :=
  congrArg RingHom.toAlgebra (nativeScalarMap_eq K n)

/-- The genuine native variety function field, with the native structural
algebra action, is the literal rational-function field in n variables. -/
def rationalFunctionFieldEquiv :
    letI := varietyFunctionFieldAlgebra (variety K n)
    (variety K n).toScheme.functionField ≃ₐ[K] FractionRing (MvPolynomial (Fin n) K) := by
  letI := varietyFunctionFieldAlgebra (variety K n)
  let e := AffineSpaceFunctionField.rationalFunctionFieldEquiv K n
  refine { __ := e.toRingEquiv, commutes' := fun c => ?_ }
  change e (functionFieldAlgebraMap (variety K n) c) = _
  rw [nativeScalarMap_eq]
  exact e.commutes c

end M9Native.AffineSpaceVariety
