module

public import M9StacksIntegration.PrimitiveParameterExtensionInvariance
public import M9StacksIntegration.PrimitiveOriginalExtensionAction
public import M9StacksIntegration.Sp6GaussIntegral
public import M9StacksIntegration.Sp6GaussChartFiniteType

@[expose] public section

/-! Genuine constant-to-extension invariance for the original native Sp6
action.  The domain and finite-type properties are proved by the actual
Gauss atlas.  No universal or geometric invariance is an input, and no
chosen rational denominator is required to survive at the extension point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveGeometricExtensionInvariance

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalExtensionPoints

/-- The actual parameter algebra is a domain by the actual Sp6 Gauss atlas. -/
instance parameter_isDomain : IsDomain TensorRing :=
  Sp6GaussIntegral.tensor_isDomain ℂ E

/-- Actual constant native pullback invariance forces the actual universal
action and projection pullbacks to agree. -/
theorem coaction_eq_projection_of_pullback_fixed (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f) :
    PrimitiveRationalCoaction.coaction f = PrimitiveRationalCoaction.projectionPullback f :=
  PrimitiveRationalCoaction.coaction_eq_projection_of_pullback_fixed f hf

/-- Every extension-valued native group point preserves the original
function value on any two related generic field embeddings. -/
theorem eq_of_constant_pullback_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  PrimitiveParameterExtensionInvariance.eq_of_constant_pullback_fixed f hf g s t ht

theorem eq_of_constant_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldAction h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  PrimitiveParameterExtensionInvariance.eq_of_constant_fixed f hf g s t ht

/-- The extension point may be given in the original exterior-model group;
its native binding and primitive-matrix formula are the checked literal ones. -/
theorem eq_of_original_action {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f)
    (g : M9.PrimitiveStabilizer.Sp6 L) (s t : E →ₐ[ℂ] L)
    (ht : (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
      (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
        NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  eq_of_constant_pullback_fixed f hf (PrimitiveOriginalExtensionAction.nativeGroupPoint g) s t ht

theorem eq_of_original_action_of_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldAction h f = f)
    (g : M9.PrimitiveStabilizer.Sp6 L) (s t : E →ₐ[ℂ] L)
    (ht : (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
      (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
        NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  eq_of_constant_fixed f hf (PrimitiveOriginalExtensionAction.nativeGroupPoint g) s t ht

end M9Native.PrimitiveGeometricExtensionInvariance
