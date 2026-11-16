module

public import M9StacksIntegration.PrimitiveUniversalFieldAction

@[expose] public section

/-! Genuine constant slices and dominance of the actual universal action.
The group slices are identified through the actual affine presentation. The
actual identity evaluation supplies a section over the generic point, proving
dominance without any assumed section or geometric-invariance premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace M9Native.PrimitiveUniversalConstantSlices

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction

def fieldToBase : fieldOver ⟶ Over.mk (𝟙 PrimitiveFamilyFreeAction.base) :=
  Over.homMk fieldOver.hom (by simp)

/-- Tensor evaluation restricts the actual universal group point to the
original base-field group point. -/
theorem slice_group_base (χ : A →ₐ[ℂ] ℂ) :
    slice χ ≫ universalGroup = fieldToBase ≫ Sp6AffinePoints.basePoint ℂ χ := by
  apply Over.OverMorphism.ext
  change
    (Spec.map (CommRingCat.ofHom (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing).toRingHom)) ≫
        (Sp6AffineBaseChange.affineIso ℂ).hom =
    (Sp6AffineBaseChange.specAlgebraMap ℂ E ≫ Spec.map (CommRingCat.ofHom χ.toRingHom)) ≫
      (Sp6AffineBaseChange.affineIso ℂ).hom
  apply (cancel_mono (Sp6AffineBaseChange.affineIso ℂ).hom).mpr
  dsimp only [Sp6AffineBaseChange.specAlgebraMap]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  change TensorEvaluationSeparation.algebraEvaluate (E := E) χ (a ⊗ₜ[ℂ] (1 : E)) =
    algebraMap ℂ E (χ a)
  simp [Algebra.smul_def]

/-- Every constant tensor slice is the literal old Sp6(C) constant point. -/
theorem slice_group (χ : A →ₐ[ℂ] ℂ) :
    slice χ ≫ universalGroup =
      PrimitiveFamilyFreeAction.constantPointOn fieldOver (Sp6AffinePoints.originalElement χ) := by
  rw [slice_group_base, ← Sp6AffinePoints.constantPoint_originalElement χ]
  rfl

/-- The actual universal scheme action restricts to the original constant
scheme automorphism at every constant algebra point. -/
theorem slice_action (χ : A →ₐ[ℂ] ℂ) :
    slice χ ≫ actionOver =
      genericOverPoint ≫ PrimitiveConstantFieldAction.overMap (Sp6AffinePoints.originalElement χ) := by
  change slice χ ≫ (lift universalGroup universalX ≫ nativeAction.act) = _
  rw [nativeAction.comp_smul, slice_group, slice_projection]
  exact (PrimitiveConstantFieldAction.overMap_comp genericOverPoint
    (Sp6AffinePoints.originalElement χ)).symm

/-- Literal generic-field-point formula of that genuine constant slice. -/
theorem slice_action_left (χ : A →ₐ[ℂ] ℂ) :
    (slice χ).left ≫ actionMap =
      NativeGenericPullbackEvaluation.point
        (PrimitiveConstantFieldAction.fieldPullback (Sp6AffinePoints.originalElement χ)).toRingHom := by
  have he := congrArg (fun q : fieldOver ⟶ overSpace => q.left) (slice_action χ)
  calc
    (slice χ).left ≫ actionMap = NativeFunctionFieldFunctor.genericSpec space ≫
        PrimitiveConstantFieldAction.schemeMap (Sp6AffinePoints.originalElement χ) := by
      change (slice χ).left ≫ actionMap = genericOverPoint.left ≫
        PrimitiveConstantFieldAction.schemeMap (Sp6AffinePoints.originalElement χ) at he
      exact he.trans (congrArg (fun q : fieldOver.left ⟶ space => q ≫
        PrimitiveConstantFieldAction.schemeMap (Sp6AffinePoints.originalElement χ)) genericOverPoint_left)
    _ = Spec.map (CommRingCat.ofHom (NativeDominantFunctionField.map
          (PrimitiveConstantFieldAction.schemeMap (Sp6AffinePoints.originalElement χ)))) ≫
        NativeFunctionFieldFunctor.genericSpec space :=
      (NativeFunctionFieldFunctor.map_square _).symm
    _ = NativeGenericPullbackEvaluation.point
        (PrimitiveConstantFieldAction.fieldPullback (Sp6AffinePoints.originalElement χ)).toRingHom := by
      rw [NativeGenericPullbackEvaluation.point, PrimitiveConstantFieldAction.fieldPullback_eq_map]

/-- The original identity element is obtained by the actual identity evaluation. -/
theorem identity_slice_group :
    slice (Sp6AffinePoints.identityEvaluation ℂ) ≫ universalGroup = 1 := by
  rw [slice_group_base, Sp6AffinePoints.basePoint_identityEvaluation]
  exact (Sp6GroupScheme.groupScheme PrimitiveFamilyFreeAction.base).comp_one fieldToBase

/-- The identity slice of the original universal action is the actual generic point. -/
theorem identity_slice_action :
    slice (Sp6AffinePoints.identityEvaluation ℂ) ≫ actionOver = genericOverPoint := by
  change slice (Sp6AffinePoints.identityEvaluation ℂ) ≫
    (lift universalGroup universalX ≫ nativeAction.act) = _
  rw [nativeAction.comp_smul, identity_slice_group, slice_projection]
  exact nativeAction.one_smul fieldOver genericOverPoint

theorem identity_slice_action_left :
    (slice (Sp6AffinePoints.identityEvaluation ℂ)).left ≫ actionMap =
      NativeFunctionFieldFunctor.genericSpec space :=
  (congrArg (fun q : fieldOver ⟶ overSpace => q.left) identity_slice_action).trans
    genericOverPoint_left

/-- Dominance follows from the actual identity slice, not from an assumed
universal action section. -/
instance actionMap_isDominant : IsDominant actionMap := by
  let : IsDominant ((slice (Sp6AffinePoints.identityEvaluation ℂ)).left ≫ actionMap) := by
    rw [identity_slice_action_left]
    infer_instance
  exact IsDominant.of_comp (f := (slice (Sp6AffinePoints.identityEvaluation ℂ)).left)
    (g := actionMap)

instance projectionMap_isDominant : IsDominant projectionMap := by
  let : IsDominant ((slice (Sp6AffinePoints.identityEvaluation ℂ)).left ≫ projectionMap) := by
    rw [slice_projection_left]
    infer_instance
  exact IsDominant.of_comp (f := (slice (Sp6AffinePoints.identityEvaluation ℂ)).left)
    (g := projectionMap)

end M9Native.PrimitiveUniversalConstantSlices
