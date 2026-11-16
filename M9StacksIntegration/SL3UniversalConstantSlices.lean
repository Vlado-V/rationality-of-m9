module

public import M9StacksIntegration.SL3UniversalFieldAction
public import M9StacksIntegration.NativeGenericPointNaturality

@[expose] public section

/-! Actual constant slices of the genuine varying connected stabilizer
family recover the frozen reduced native action and its field pullback. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
open scoped TensorProduct

namespace M9Native.SL3UniversalConstantSlices

open SL3UniversalFieldAction

theorem slice_groupMatrix (χ : A →ₐ[ℂ] ℂ) :
    Matrix.SpecialLinearGroup.map
      (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom universalGroupMatrix =
        Matrix.SpecialLinearGroup.map (algebraMap ℂ E) (SL3CoordinateRing.homEquiv ℂ χ) := by
  rw [universalGroupMatrix, ← SL3CoordinateRing.homEquiv_comp]
  have he : (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorRing) =
      (Algebra.ofId ℂ E).comp χ := by
    ext a
    simp [Algebra.smul_def]
  rw [he, SL3CoordinateRing.homEquiv_comp]
  rfl

theorem slice_matrix (χ : A →ₐ[ℂ] ℂ) :
    Matrix.SpecialLinearGroup.map (slice χ).left.appTop.hom universalMatrix =
      Matrix.SpecialLinearGroup.map (SL3FamilyFreeAction.scalarMap fieldOver)
        (SL3CoordinateRing.homEquiv ℂ χ) := by
  have h := specMap_matrix
    (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom universalGroupMatrix
  rw [slice_groupMatrix] at h
  change Matrix.SpecialLinearGroup.map (slice χ).left.appTop.hom universalMatrix = _
  apply h.trans
  rw [scalarMap_spec]
  apply Subtype.ext
  ext i j
  rfl

def constantOverMap (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : overSpace ⟶ overSpace :=
  Over.homMk (ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inl g))
    (ReducedGraphAction.nativeAction_projection ℂ _)

/-- Constant scheme slices give the original reduced native action. -/
theorem slice_action (χ : A →ₐ[ℂ] ℂ) :
    slice χ ≫ actionOver = genericOverPoint ≫ constantOverMap (SL3CoordinateRing.homEquiv ℂ χ) := by
  apply Over.OverMorphism.ext
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · exact (slice χ ≫ actionOver).w.trans
      (genericOverPoint ≫ constantOverMap (SL3CoordinateRing.homEquiv ℂ χ)).w.symm
  · change GraphGrassmannianLinearAction.pointClass ℂ ((slice χ).left ≫ actionMap) =
      GraphGrassmannianLinearAction.pointClass ℂ (genericOverPoint.left ≫
        ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ)))
    have hp : (slice χ).left ≫ projectionMap = genericOverPoint.left :=
      (slice_projection_left χ).trans genericOverPoint_left.symm
    rw [action_pointClass_natural, slice_matrix, SL3FamilyFreeAction.transformPoints_constant,
      hp, ReducedGraphAction.nativeAction_classifier]
    exact congrArg (fun b : fieldOver.left ⟶ SL3FamilyFreeAction.base =>
      GraphGrassmannianLinearAction.transformPoints ℂ b
        (ReducedGraphAction.matrixRepresentation ℂ
          (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ)))
        (GraphGrassmannianLinearAction.pointClass ℂ genericOverPoint.left)) genericOverPoint.w.symm

theorem slice_action_left (χ : A →ₐ[ℂ] ℂ) :
    (slice χ).left ≫ actionMap = NativeFunctionFieldFunctor.genericSpec space ≫
      ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ)) := by
  have h := congrArg (fun q : fieldOver ⟶ overSpace => q.left) (slice_action χ)
  exact h.trans (congrArg (fun q : fieldOver.left ⟶ space => q ≫
    ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ)))
      genericOverPoint_left)

/-- These are the actual field pullbacks of the original reduced action. -/
theorem slice_action_field_point (χ : A →ₐ[ℂ] ℂ) :
    (slice χ).left ≫ actionMap = NativeGenericPullbackEvaluation.point
      (ReducedGraphAction.nativeFieldRepresentation ℂ
        (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ))).toRingHom := by
  rw [slice_action_left]
  have h := NativeGenericPointNaturality.point_comp_dominant
    (ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ)))
      (RingHom.id E)
  have hi : NativeGenericPullbackEvaluation.point (RingHom.id E) =
      NativeFunctionFieldFunctor.genericSpec space := genericOverPoint_left
  rw [hi, RingHom.id_comp, ← ReducedGraphAction.nativeFieldRepresentation_eq_map] at h
  exact h

theorem identity_slice_action :
    (slice (SL3CoordinateRing.evaluation ℂ (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ))).left ≫
      actionMap = NativeFunctionFieldFunctor.genericSpec space := by
  rw [slice_action_left, show SL3CoordinateRing.homEquiv ℂ
      (SL3CoordinateRing.evaluation ℂ (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ)) = 1 from
        (SL3CoordinateRing.homEquiv ℂ).apply_symm_apply 1,
    map_one, ReducedGraphAction.nativeAction_one, Category.comp_id]

instance actionMap_isDominant : IsDominant actionMap := by
  let : IsDominant ((slice (SL3CoordinateRing.evaluation ℂ
      (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ))).left ≫ actionMap) := by
    rw [identity_slice_action]
    infer_instance
  exact IsDominant.of_comp (f := (slice (SL3CoordinateRing.evaluation ℂ
    (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ))).left) (g := actionMap)

instance projectionMap_isDominant : IsDominant projectionMap := by
  let : IsDominant ((slice (SL3CoordinateRing.evaluation ℂ
      (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ))).left ≫ projectionMap) := by
    rw [slice_projection_left]
    infer_instance
  exact IsDominant.of_comp (f := (slice (SL3CoordinateRing.evaluation ℂ
    (1 : Matrix.SpecialLinearGroup (Fin 3) ℂ))).left) (g := projectionMap)

end M9Native.SL3UniversalConstantSlices
