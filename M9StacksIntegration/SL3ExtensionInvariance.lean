module

public import M9StacksIntegration.SL3UniversalConstantSlices
public import M9StacksIntegration.NativeTensorInvariantPullback
public import M9StacksIntegration.NativeAffineGenericSquare

@[expose] public section

/-! Genuine constant-to-extension invariance for the actual connected
stabilizer family and the full stabilizer with its constant odd component.
All group-coordinate domain, finite-type and evaluation-separation inputs
are proved for the literal determinant-one coordinate ring.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace M9Native.SL3ExtensionInvariance

open SL3UniversalFieldAction SL3UniversalConstantSlices
open NativePullbackFractionEvaluation NativeGenericPullbackEvaluation

abbrev F : Type := parameter.functionField
abbrev parameterProjection : parameter ⟶ Spec (.of ℂ) := parameterOver.hom

instance parameterBaseAlgebra : Algebra TensorRing F :=
  GrassmannianCharts.affineFunctionField_ringAlgebra TensorRing

instance parameterIsFractionRing : IsFractionRing TensorRing F :=
  GrassmannianCharts.affineFunctionField_isFractionRing TensorRing

instance parameterComplexAlgebra : Algebra ℂ F :=
  (GrassmannianCharts.structureScalarMap ℂ parameterProjection).toAlgebra

def coefficientInclusion : TensorRing →+* F :=
  @algebraMap TensorRing F _ _ parameterBaseAlgebra

def coaction : E →ₐ[ℂ] F where
  __ := NativeDominantFunctionField.map actionMap
  commutes' c := by
    have h := NativeDominantFunctionField.map_scalar ℂ actionMap projection
    rw [show actionMap ≫ projection = parameterProjection from actionOver.w] at h
    exact DFunLike.congr_fun h c

def projectionPullback : E →ₐ[ℂ] F where
  __ := NativeDominantFunctionField.map projectionMap
  commutes' c := by
    have h := NativeDominantFunctionField.map_scalar ℂ projectionMap projection
    rw [show projectionMap ≫ projection = parameterProjection from universalX.w] at h
    exact DFunLike.congr_fun h c

theorem projectionPullback_apply (f : E) :
    projectionPullback f = coefficientInclusion (1 ⊗ₜ[ℂ] f) := by
  have hi : point (RingHom.id E) = NativeFunctionFieldFunctor.genericSpec space :=
    genericOverPoint_left
  have hs (χ : A →ₐ[ℂ] ℂ) : (slice χ).left ≫ projectionMap = point (RingHom.id E) :=
    (slice_projection_left χ).trans hi.symm
  have ha (χ : A →ₐ[ℂ] ℂ) :
      projectionMap (Spec.map (CommRingCat.ofHom
        (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom)
          (IsLocalRing.closedPoint E)) = genericPoint space := by
    have h := congrArg (fun q : Spec (.of E) ⟶ space => q (IsLocalRing.closedPoint E)) (hs χ)
    exact h.trans (point_apply _ _)
  have hc (χ : A →ₐ[ℂ] ℂ) : pointPullback projectionMap (slice χ).left (ha χ) f = f :=
    DFunLike.congr_fun (pointPullback_of_point projectionMap (slice χ).left
      (RingHom.id E) (hs χ) (ha χ)) f
  exact NativeTensorInvariantPullback.pullback_eq_coefficient ℂ A E projectionMap ha f f hc

/-- Actual constant connected fixedness forces actual universal coaction equality. -/
theorem coaction_eq_projection_of_constant_fixed (f : E)
    (hf : ∀ g : Matrix.SpecialLinearGroup (Fin 3) ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ (SemidirectProduct.inl g) f = f) :
    coaction f = projectionPullback f := by
  have ha (χ : A →ₐ[ℂ] ℂ) :
      actionMap (Spec.map (CommRingCat.ofHom
        (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom)
          (IsLocalRing.closedPoint E)) = genericPoint space := by
    have h := congrArg (fun q : Spec (.of E) ⟶ space => q (IsLocalRing.closedPoint E))
      (slice_action_field_point χ)
    exact h.trans (point_apply _ _)
  have hc (χ : A →ₐ[ℂ] ℂ) :
      pointPullback actionMap (Spec.map (CommRingCat.ofHom
        (TensorEvaluationSeparation.algebraEvaluate (E := E) χ).toRingHom)) (ha χ) f = f := by
    exact (DFunLike.congr_fun (pointPullback_of_point actionMap _
      (ReducedGraphAction.nativeFieldRepresentation ℂ
        (SemidirectProduct.inl (SL3CoordinateRing.homEquiv ℂ χ))).toRingHom
          (slice_action_field_point χ) (ha χ)) f).trans (hf _)
  exact (NativeTensorInvariantPullback.pullback_eq_coefficient ℂ A E actionMap ha f f hc).trans
    (projectionPullback_apply f).symm

/-- No extension-valued invariance is assumed: it follows at the original
two generic field embeddings from constant complex fixedness. -/
theorem eq_of_constant_connected_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ g : Matrix.SpecialLinearGroup (Fin 3) ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ (SemidirectProduct.inl g) f = f)
    (g : Matrix.SpecialLinearGroup (Fin 3) L) (s t : E →ₐ[ℂ] L)
    (ht : (parameterPoint g s).left ≫ actionMap = point t.toRingHom) : s f = t f := by
  have h := coaction_eq_projection_of_constant_fixed f hf
  change NativeDominantFunctionField.map actionMap f =
    NativeDominantFunctionField.map projectionMap f at h
  exact (eq_at_generic_points_of_pullbacks_eq actionMap projectionMap (parameterPoint g s).left
    t.toRingHom s.toRingHom ht (parameterPoint_projection_left g s) f h).symm

def fullActionMap (c : M9.CentralSignQuotient.C2) : parameter ⟶ space :=
  actionMap ≫ ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c)

instance fullActionMap_isDominant (c : M9.CentralSignQuotient.C2) :
    IsDominant (fullActionMap c) := by
  unfold fullActionMap
  infer_instance

theorem full_pullback_eq_projection_of_constant_fixed (f : E)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (c : M9.CentralSignQuotient.C2) :
    NativeDominantFunctionField.map (fullActionMap c) f = NativeDominantFunctionField.map projectionMap f := by
  change NativeDominantFunctionField.map
    (actionMap ≫ ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c)) f = _
  rw [show NativeDominantFunctionField.map
      (actionMap ≫ ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c)) =
      (NativeDominantFunctionField.map actionMap).comp
        (NativeDominantFunctionField.map (ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c))) from
          NativeFunctionFieldFunctor.map_comp _ _]
  have hc : NativeDominantFunctionField.map
      (ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c)) f = f :=
    (DFunLike.congr_fun (ReducedGraphAction.nativeFieldRepresentation_eq_map ℂ _).symm f).trans (hf _)
  rw [RingHom.comp_apply, hc]
  exact coaction_eq_projection_of_constant_fixed f (fun g => hf (SemidirectProduct.inl g))

/-- Full actual H(L)=SL3(L) semidirect C2 promotion, with its genuine
constant odd component.  The actual native family relation is the only point input. -/
theorem eq_of_constant_H_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ w : ReducedGraphAction.Stabilizer ℂ,
      ReducedGraphAction.nativeFieldRepresentation ℂ w f = f)
    (g : Matrix.SpecialLinearGroup (Fin 3) L) (c : M9.CentralSignQuotient.C2)
    (s t : E →ₐ[ℂ] L)
    (ht : (parameterPoint g s).left ≫ fullActionMap c = point t.toRingHom) : s f = t f := by
  exact (eq_at_generic_points_of_pullbacks_eq (fullActionMap c) projectionMap (parameterPoint g s).left
    t.toRingHom s.toRingHom ht (parameterPoint_projection_left g s) f
      (full_pullback_eq_projection_of_constant_fixed f hf c)).symm

end M9Native.SL3ExtensionInvariance
