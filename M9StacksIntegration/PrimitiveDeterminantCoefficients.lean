module

public import M9StacksIntegration.PrimitiveDecomposableNonzero

/-!
# Literal determinant evaluation in the original fourteen primitive coordinates

Any actual exterior evaluation annihilating the original sigma-wedge
descends through the checked native primitive quotient. The resulting
coefficient formula uses the original primitive basis and the actual
independent-triple coefficients; it requires no complete-section basis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module
open scoped BigOperators

universe u v

namespace M9Native.PrimitiveDeterminantCoefficients

open LagrangianField MukaiPrimitiveDuality MukaiConormalPrimitive

variable (K : Type u) [Field K] [CharZero K]
  {T : Type v} [AddCommGroup T] [Module K T]

/-- The original quotient factor recovers every original exterior evaluation. -/
theorem factor_primitiveClass (L : Third K →ₗ[K] T)
    (hσ : ∀ v, L (wedgeSigma K v) = 0) (w : Third K) :
    factor K L (primitiveClass K w) = L w :=
  (factor_restriction K L hσ (coefficientDuality K w)).trans
    (congrArg L ((coefficientDuality K).symm_apply_apply w))

/-- The actual primitive class of a triple has precisely the original fourteen coefficients. -/
theorem primitiveClass_expansion (s : Fin 3 → V K) :
    primitiveClass K (exteriorPower.ιMulti K 3 s) =
      ∑ j : Fin 14, PrimitiveDecomposableNonzero.coefficients K s j •
        (LagrangianPluckerLinear.primitiveBasis14 K).dualBasis j := by
  simpa only [PrimitiveDecomposableNonzero.coefficients, Module.Basis.dualBasis_repr] using
    ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis.sum_repr
      (primitiveClass K (exteriorPower.ιMulti K 3 s))).symm

/-- Every genuine sigma-annihilating evaluation has the literal original coefficient sum. -/
theorem evaluation_ιMulti_eq_sum (L : Third K →ₗ[K] T)
    (hσ : ∀ v, L (wedgeSigma K v) = 0) (s : Fin 3 → V K) :
    L (exteriorPower.ιMulti K 3 s) =
      ∑ j : Fin 14, PrimitiveDecomposableNonzero.coefficients K s j •
        factor K L ((LagrangianPluckerLinear.primitiveBasis14 K).dualBasis j) := by
  rw [← factor_primitiveClass K L hσ, primitiveClass_expansion]
  simp only [map_sum, map_smul]

end M9Native.PrimitiveDeterminantCoefficients
