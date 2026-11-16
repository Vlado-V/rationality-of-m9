module

public import M9StacksIntegration.PrimitiveRationalCoaction
public import M9StacksIntegration.PrimitiveUniversalExtensionPoints

@[expose] public section

/-! Actual all-field invariance from constant native Sp6 invariance.

The only geometric inputs are the real properties of the original group
algebra and tensor parameter algebra, pending the group-geometry provider.
There is no assumed geometric invariance, universal pullback equality, or
nonvanishing of a chosen universal denominator at extension-valued points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveExtensionInvariance

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalConstantSlices
open PrimitiveUniversalExtensionPoints

variable [IsDomain TensorRing] [IsReduced A] [Algebra.FiniteType ℂ A]

/-- The actual native action on arbitrary generic extension-field points
preserves every function fixed by all original constant scheme pullbacks. -/
theorem eq_of_constant_pullback_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f := by
  have hfield := PrimitiveRationalCoaction.coaction_eq_projection_of_pullback_fixed f hf
  change NativeDominantFunctionField.map actionMap f =
    NativeDominantFunctionField.map projectionMap f at hfield
  exact (NativeGenericPullbackEvaluation.eq_at_generic_points_of_pullbacks_eq
    actionMap projectionMap (parameterPoint g s).left t.toRingHom s.toRingHom
    (parameterPoint_action_of_relation g s t ht) (parameterPoint_projection_left g s) f hfield).symm

/-- The equivalent statement for the original actual left field-action convention. -/
theorem eq_of_constant_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldAction h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  eq_of_constant_pullback_fixed f ((PrimitiveConstantFieldAction.fixed_iff_pullback_fixed f).mp hf)
    g s t ht

end M9Native.PrimitiveExtensionInvariance
