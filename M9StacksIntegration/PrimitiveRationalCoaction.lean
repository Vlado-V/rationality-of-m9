module

public import M9StacksIntegration.PrimitiveUniversalConstantSlices
public import M9StacksIntegration.NativeAffineGenericSquare
public import M9StacksIntegration.NativeAffinePullbackEvaluation
public import M9StacksIntegration.ConstantPointRationalEquality

@[expose] public section

/-! Actual native rational coaction and constant-point invariance.

The group and parameter algebras are the original concrete algebras. The
geometric properties below remain explicit inputs until the group-geometry
provider supplies them: no universal invariance or field-point invariance is
an input. The coaction is the actual native dominant generic-stalk pullback.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace M9Native.PrimitiveRationalCoaction

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalConstantSlices
open NativePullbackFractionEvaluation NativeGenericPullbackEvaluation

variable [IsDomain TensorRing]

abbrev F := parameter.functionField

abbrev parameterProjection : parameter ⟶ Spec (.of ℂ) := parameterOver.hom

/-- The actual affine fraction-field structure, exposed at the concrete parameter type. -/
instance parameterBaseAlgebra : Algebra TensorRing F :=
  GrassmannianCharts.affineFunctionField_ringAlgebra TensorRing

instance parameterIsFractionRing : IsFractionRing TensorRing F :=
  GrassmannianCharts.affineFunctionField_isFractionRing TensorRing

/-- The original structural complex algebra on the actual parameter function field. -/
instance parameterComplexAlgebra : Algebra ℂ F :=
  (GrassmannianCharts.structureScalarMap ℂ parameterProjection).toAlgebra

/-- The actual universal-action pullback, with its original complex scalars. -/
def coaction : E →ₐ[ℂ] F where
  __ := NativeDominantFunctionField.map actionMap
  commutes' c := by
    have he := NativeDominantFunctionField.map_scalar ℂ actionMap projection
    rw [show actionMap ≫ projection = parameterProjection from actionOver.w] at he
    exact DFunLike.congr_fun he c

/-- The actual generic-projection pullback with the same original scalars. -/
def projectionPullback : E →ₐ[ℂ] F where
  __ := NativeDominantFunctionField.map projectionMap
  commutes' c := by
    have he := NativeDominantFunctionField.map_scalar ℂ projectionMap projection
    rw [show projectionMap ≫ projection = parameterProjection from universalX.w] at he
    exact DFunLike.congr_fun he c

private theorem map_congr {a b : parameter ⟶ space} [IsDominant a] [IsDominant b]
    (h : a = b) : NativeDominantFunctionField.map a = NativeDominantFunctionField.map b := by
  subst b
  rfl

/-- The genuine projection pullback is the literal tensor-coefficient inclusion. -/
theorem projectionPullback_apply (f : E) :
    projectionPullback f = algebraMap TensorRing F (1 ⊗ₜ[ℂ] f) := by
  let φ : E →+* TensorRing :=
    (Algebra.TensorProduct.includeRight : E →ₐ[ℂ] TensorRing).toRingHom
  let : IsDominant (Spec.map (CommRingCat.ofHom φ)) :=
    NativeDominantFunctionField.specMap_isDominant φ φ.injective
  have hproj : projectionMap =
      Spec.map (CommRingCat.ofHom φ) ≫ NativeFunctionFieldFunctor.genericSpec space := by
    change Spec.map (CommRingCat.ofHom φ) ≫ genericOverPoint.left = _
    exact congrArg (fun q : fieldOver.left ⟶ space => Spec.map (CommRingCat.ofHom φ) ≫ q)
      genericOverPoint_left
  change NativeDominantFunctionField.map projectionMap f = _
  calc
    NativeDominantFunctionField.map projectionMap f =
        NativeDominantFunctionField.map
          (Spec.map (CommRingCat.ofHom φ) ≫ NativeFunctionFieldFunctor.genericSpec space) f :=
      DFunLike.congr_fun (map_congr hproj) f
    _ = NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom φ))
        (NativeDominantFunctionField.map (NativeFunctionFieldFunctor.genericSpec space) f) :=
      DFunLike.congr_fun (NativeFunctionFieldFunctor.map_comp _ _) f
    _ = NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom φ))
        (algebraMap E (Spec space.functionField).functionField f) :=
      congrArg (NativeDominantFunctionField.map (Spec.map (CommRingCat.ofHom φ)))
        (DFunLike.congr_fun NativeAffineGenericSquare.map_genericSpec f)
    _ = algebraMap TensorRing F (φ f) := NativeFunctionFieldFunctor.affine_map_algebraMap φ f
    _ = algebraMap TensorRing F (1 ⊗ₜ[ℂ] f) := rfl

section Separation

variable [IsReduced A] [Algebra.FiniteType ℂ A]

/-- Actual constant scheme-pullback invariance forces the actual universal
coaction to be the original coefficient image. -/
theorem coaction_constant_of_pullback_fixed (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f) :
    coaction f = algebraMap TensorRing F (1 ⊗ₜ[ℂ] f) := by
  obtain ⟨n, d, hdmem, hrep⟩ := IsFractionRing.div_surjective TensorRing (coaction f)
  have hd : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hdmem
  have hιd : algebraMap TensorRing F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdmem
  have hconst (χ : A →ₐ[ℂ] ℂ) :
      TensorEvaluationSeparation.algebraEvaluate (E := E) χ n =
        f * TensorEvaluationSeparation.algebraEvaluate (E := E) χ d := by
    let κ := TensorEvaluationSeparation.algebraEvaluate (E := E) χ
    let h := Sp6AffinePoints.originalElement χ
    let p := Spec.map (CommRingCat.ofHom κ.toRingHom)
    have hs : p ≫ actionMap = point (PrimitiveConstantFieldAction.fieldPullback h).toRingHom :=
      slice_action_left χ
    have ha : actionMap (p (IsLocalRing.closedPoint E)) = genericPoint space := by
      have he := congrArg (fun q : Spec (.of E) ⟶ space => q (IsLocalRing.closedPoint E)) hs
      exact he.trans (point_apply (PrimitiveConstantFieldAction.fieldPullback h).toRingHom _)
    have hc := NativeAffinePullbackEvaluation.cross_identity_of_fraction_at_affine_point
      TensorRing actionMap κ.toRingHom ha f n d hd hrep.symm
    have hp : pointPullback actionMap p ha f = f :=
      (DFunLike.congr_fun (pointPullback_of_point actionMap p
        (PrimitiveConstantFieldAction.fieldPullback h).toRingHom hs ha) f).trans (hf h)
    exact hc.symm.trans (congrArg (fun q : E => q * κ d) hp)
  have hnd : n = (1 ⊗ₜ[ℂ] f) * d :=
    ConstantPointRationalEquality.eq_mul_denominator_of_constant_cross_eq_of_ne_zero hd f
      (fun χ _ => hconst χ)
  calc
    coaction f = algebraMap TensorRing F n / algebraMap TensorRing F d := hrep.symm
    _ = algebraMap TensorRing F (1 ⊗ₜ[ℂ] f) := by
      rw [hnd, map_mul, mul_div_cancel_right₀ _ hιd]

/-- No geometric invariance is assumed: equality of the two actual native
pullbacks is derived from the original constant-point invariance. -/
theorem coaction_eq_projection_of_pullback_fixed (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f) :
    coaction f = projectionPullback f :=
  (coaction_constant_of_pullback_fixed f hf).trans (projectionPullback_apply f).symm

theorem coaction_eq_projection_of_fixed (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldAction h f = f) :
    coaction f = projectionPullback f :=
  coaction_eq_projection_of_pullback_fixed f
    ((PrimitiveConstantFieldAction.fixed_iff_pullback_fixed f).mp hf)

end Separation

end M9Native.PrimitiveRationalCoaction
