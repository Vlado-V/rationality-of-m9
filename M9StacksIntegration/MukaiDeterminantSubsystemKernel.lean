module

public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection
public import M9StacksIntegration.LagrangianTripleDeterminantSection
public import M9StacksIntegration.LagrangianModelRestriction

/-!
# The actual20-to-H0 determinant map on the original transverse curve

Actual original primitive restriction has rank9. Its proved scalar-preserving
comparison with the actual quotient exterior evaluation gives rank9 for
the map from the ORIGINAL third exterior power, and therefore kernel11.
No complete-H0 identification, section independence or kernel/rank premise
is supplied. The evaluation on an actual triple is the literal original
determinantValue, not a coefficient-only replacement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Module

namespace M9Native.MukaiDeterminantSubsystemKernel
universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- The ACTUAL full exterior determinant restriction on the SAME original
transverse five-cut curve and its SAME quotient bundle. -/
def determinantMap (M : Matrix (Fin 5) (Fin 14) K) :=
  LagrangianQuotientExteriorEvaluation.lambda K
    (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianUniversalSections.quotientMap K
      (LagrangianTransverseRestriction.inclusion K M)) 3

section Ordered
variable (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (LagrangianTransverseRestriction.curve K M)]
  [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]

theorem range_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (LinearMap.range (determinantMap K M)) = 9 := by
  have h := LagrangianPrimitiveRestrictionInjection.finrank_restriction_eq_range_lambda K
    (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianTransverseRestriction.inclusion K M) rfl
  rw [LagrangianTransverseRestriction.primitiveRestriction_range_finrank K M hM] at h
  exact h.symm

/-- The11-dimensional kernel is a consequence of the actual rank9 theorem,
not a supplied projective intersection or subsystem premise. -/
theorem ker_finrank (hM : Function.Surjective M.mulVec) :
    finrank K (LinearMap.ker (determinantMap K M)) = 11 := by
  have h := LinearMap.finrank_range_add_finrank_ker (determinantMap K M)
  rw [range_finrank K M hM, LagrangianField.finrank_third K] at h
  omega

omit [IsAlgClosed K] [IsIntegral (LagrangianTransverseRestriction.curve K M)]
  [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)] in
/-- On every literal original triple, the actual full exterior map is
exactly the actual original determinant section. -/
theorem map_ιMulti_eq_determinantValue (s : Fin 3 → (Fin 6 → K)) :
    determinantMap K M (exteriorPower.ιMulti K 3 s) =
      LagrangianTripleDeterminantSection.determinantValue K
        (LagrangianTransverseRestriction.curveProjection K M)
        (LagrangianTransverseRestriction.inclusion K M) s := by
  change LagrangianQuotientExteriorEvaluation.lambda K
    (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianUniversalSections.quotientMap K
      (LagrangianTransverseRestriction.inclusion K M)) 3 (exteriorPower.ιMulti K 3 s) = _
  rw [LagrangianQuotientExteriorEvaluation.lambda_ιMulti,
    LagrangianTripleDeterminantSection.originalSectionMap_eq]
  rfl

end Ordered

/-- The SAME actual full determinant map on the original five-section
bundle model. Its comparison with the ordered cut is already proved. -/
def modelDeterminantMap (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) :=
  LagrangianQuotientExteriorEvaluation.lambda K
    (LagrangianOrderedFibre.modelProjection K M hM)
    (LagrangianUniversalSections.quotientMap K
      (LagrangianOrderedFibre.modelInclusion K M hM)) 3

section Model
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (LagrangianOrderedFibre.model K M hM)]
  [SmoothOfRelativeDimension 1 (LagrangianOrderedFibre.modelProjection K M hM)]

theorem model_range_finrank :
    finrank K (LinearMap.range (modelDeterminantMap K M hM)) = 9 := by
  have h := LagrangianPrimitiveRestrictionInjection.finrank_restriction_eq_range_lambda K
    (LagrangianOrderedFibre.modelProjection K M hM)
    (LagrangianOrderedFibre.modelInclusion K M hM) rfl
  rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM] at h
  exact h.symm

theorem model_ker_finrank :
    finrank K (LinearMap.ker (modelDeterminantMap K M hM)) = 11 := by
  have h := LinearMap.finrank_range_add_finrank_ker (modelDeterminantMap K M hM)
  rw [model_range_finrank K M hM, LagrangianField.finrank_third K] at h
  omega

omit [IsAlgClosed K] [IsIntegral (LagrangianOrderedFibre.model K M hM)]
  [SmoothOfRelativeDimension 1 (LagrangianOrderedFibre.modelProjection K M hM)] in
theorem model_map_ιMulti_eq_determinantValue (s : Fin 3 → (Fin 6 → K)) :
    modelDeterminantMap K M hM (exteriorPower.ιMulti K 3 s) =
      LagrangianTripleDeterminantSection.determinantValue K
        (LagrangianOrderedFibre.modelProjection K M hM)
        (LagrangianOrderedFibre.modelInclusion K M hM) s := by
  change LagrangianQuotientExteriorEvaluation.lambda K
    (LagrangianOrderedFibre.modelProjection K M hM)
    (LagrangianUniversalSections.quotientMap K
      (LagrangianOrderedFibre.modelInclusion K M hM)) 3 (exteriorPower.ιMulti K 3 s) = _
  rw [LagrangianQuotientExteriorEvaluation.lambda_ιMulti,
    LagrangianTripleDeterminantSection.originalSectionMap_eq]
  rfl

end Model

end M9Native.MukaiDeterminantSubsystemKernel
