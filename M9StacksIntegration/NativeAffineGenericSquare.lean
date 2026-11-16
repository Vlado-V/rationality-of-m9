module

public import M9StacksIntegration.NativeFunctionFieldFunctor

@[expose] public section

/-! The original affine fraction inclusion is the actual generic-point map,
and pullback along the generic-point morphism is that literal inclusion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.NativeAffineGenericSquare

open NativeFunctionFieldFunctor

theorem genericSpec_affine (R : CommRingCat.{u}) [IsDomain R] :
    genericSpec (Spec R) =
      Spec.map (show R ⟶ (Spec R).functionField from
        CommRingCat.ofHom (algebraMap R (Spec R).functionField)) :=
  Spec.fromSpecStalk_eq' R (genericPoint (Spec R))

/-- The actual native generic-stalk pullback of the generic point is the
original coefficient field's inclusion into its affine function field. -/
theorem map_genericSpec {X : Scheme.{u}} [IsIntegral X] :
    NativeDominantFunctionField.map (genericSpec X) =
      algebraMap X.functionField (Spec X.functionField).functionField := by
  have he :
      (show X.functionField ⟶ (Spec X.functionField).functionField from
        CommRingCat.ofHom (NativeDominantFunctionField.map (genericSpec X))) =
      (show X.functionField ⟶ (Spec X.functionField).functionField from
        CommRingCat.ofHom (algebraMap X.functionField (Spec X.functionField).functionField)) := by
    apply Spec.map_injective
    apply (cancel_mono (genericSpec X)).mp
    rw [map_square]
    exact congrArg (fun q => q ≫ genericSpec X) (genericSpec_affine X.functionField)
  exact congrArg CommRingCat.Hom.hom he

end M9Native.NativeAffineGenericSquare
