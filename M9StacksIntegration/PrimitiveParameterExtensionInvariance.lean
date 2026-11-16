module

public import M9StacksIntegration.PrimitiveExtensionInvariance
public import M9StacksIntegration.PrimitiveParameterGeometry

@[expose] public section

/-! The actual tensor-domain property already forces reducedness of the
original group algebra. Only the genuine parameter-domain and original
finite-type providers remain as geometric inputs in this interface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveParameterExtensionInvariance

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalExtensionPoints

variable [IsDomain TensorRing] [Algebra.FiniteType ℂ A]

theorem eq_of_constant_pullback_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldPullback h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f := by
  let : IsReduced A := PrimitiveParameterGeometry.group_isReduced_of_parameter_domain
  exact PrimitiveExtensionInvariance.eq_of_constant_pullback_fixed f hf g s t ht

theorem eq_of_constant_fixed {L : Type} [Field L] [Algebra ℂ L]
    (f : E)
    (hf : ∀ h : PrimitiveConstantFieldAction.Sp6, PrimitiveConstantFieldAction.fieldAction h f = f)
    (g : overField L ⟶ group) (s t : E →ₐ[ℂ] L)
    (ht : (lift g (NativeGenericFieldPoints.overPoint ℂ projection rfl s) ≫ nativeAction.act).left =
      NativeGenericPullbackEvaluation.point t.toRingHom) :
    s f = t f :=
  eq_of_constant_pullback_fixed f ((PrimitiveConstantFieldAction.fixed_iff_pullback_fixed f).mp hf)
    g s t ht

end M9Native.PrimitiveParameterExtensionInvariance
