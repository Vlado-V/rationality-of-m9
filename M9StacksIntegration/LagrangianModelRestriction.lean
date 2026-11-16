module

public import M9StacksIntegration.LagrangianOrderedFibre
public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianRestrictionIso

/-! The original fourteen-section restriction on the literal
five-section bundle model.  Its ordered-cut comparison is constructed,
and its prefix geometry is derived from actual transversality. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.LagrangianModelRestriction

open LagrangianOrderedFibre LagrangianPrimitiveSystem

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
variable [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

include hM in
omit [IsAlgClosed K] [SmoothOfRelativeDimension 1 (modelProjection K M hM)] in
theorem ordered_integral : IsIntegral (LagrangianTransverseRestriction.curve K M) :=
  IsIntegral.of_isIso (cutIsoModel K M hM).inv

include hM in
omit [IsAlgClosed K] [IsIntegral (model K M hM)] in
theorem ordered_smooth :
    SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M) := by
  have h : SmoothOfRelativeDimension (0 + 1)
      ((cutIsoModel K M hM).hom ≫ modelProjection K M hM) := inferInstance
  rw [cutIsoModel_hom_base] at h
  exact h

/-- The exact original five rows are the kernel on the actual model
used by the universal-quotient and conormal constructions. -/
theorem primitiveRestriction_kernel :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM)) =
        Submodule.span K (Set.range M) := by
  let : IsIntegral (LagrangianTransverseRestriction.curve K M) := ordered_integral K M hM
  let : SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M) :=
    ordered_smooth K M hM
  have he := LagrangianRestrictionIso.primitiveRestriction_kernel_iso K
    (LagrangianTransverseRestriction.curveProjection K M) (modelProjection K M hM)
    (LagrangianTransverseRestriction.inclusion K M) (modelInclusion K M hM) rfl rfl
    (cutIsoModel K M hM) (cutIsoModel_hom_toLG K M hM)
  rw [← he]
  exact LagrangianTransverseRestriction.primitiveRestriction_kernel K M hM

theorem primitiveRestriction_kernel_finrank :
    finrank K (LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM))) = 5 := by
  rw [primitiveRestriction_kernel K M hM]
  have hr := (Matrix.mulVec_surjective_iff_rank_eq_card (M := M)).mp hM
  rw [Matrix.rank_eq_finrank_span_row] at hr
  exact hr

theorem primitiveRestriction_range_finrank :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM))) = 9 := by
  have hd := (LagrangianPrimitiveRestriction.primitiveRestriction K
    (modelProjection K M hM) (modelInclusion K M hM)).finrank_range_add_finrank_ker
  rw [primitiveRestriction_kernel_finrank K M hM] at hd
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [h14] at hd
  omega

theorem primitiveH0_span_finrank :
    finrank K (Submodule.span K (Set.range
      (LagrangianPrimitiveRestriction.sectionH0 K
        (modelProjection K M hM) (modelInclusion K M hM)))) = 9 := by
  rw [← LagrangianPrimitiveRestriction.primitiveRestriction_range]
  exact primitiveRestriction_range_finrank K M hM

/-- A nonzero actual vanishing primitive vector is a nonzero actual
combination of the five original defining rows. -/
theorem exists_nonzero_vecMul_of_restriction_eq_zero (v : Fin 14 → K)
    (hv : LagrangianPrimitiveRestriction.primitiveRestriction K
      (modelProjection K M hM) (modelInclusion K M hM) v = 0) (hv0 : v ≠ 0) :
    ∃ a : Fin 5 → K, a ≠ 0 ∧ v = Matrix.vecMul a M := by
  let : IsIntegral (LagrangianTransverseRestriction.curve K M) := ordered_integral K M hM
  let : SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M) :=
    ordered_smooth K M hM
  have he := LagrangianRestrictionIso.primitiveRestriction_kernel_iso K
    (LagrangianTransverseRestriction.curveProjection K M) (modelProjection K M hM)
    (LagrangianTransverseRestriction.inclusion K M) (modelInclusion K M hM) rfl rfl
    (cutIsoModel K M hM) (cutIsoModel_hom_toLG K M hM)
  have hz : v ∈ LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (LagrangianTransverseRestriction.curveProjection K M)
      (LagrangianTransverseRestriction.inclusion K M)) := by
    rw [he]
    exact hv
  exact LagrangianTransverseRestriction.exists_nonzero_vecMul_of_restriction_eq_zero
    K M hM v hz hv0

end M9Native.LagrangianModelRestriction
end
