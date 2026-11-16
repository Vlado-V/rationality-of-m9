module

public import M9StacksIntegration.MukaiConormalPositivePoint
public import M9StacksIntegration.MukaiQuarticGradientTransport

/-! The actual inverse-dual local gradient points along the actual
positive native Plucker vector in the same translated-origin frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Module Matrix

namespace M9Native.MukaiCubicPositivePoint

open LagrangianField MukaiQuarticGradientTransport MukaiConormalPositivePoint
open LagrangianTranslatedDeterminantCoordinates

variable (K : Type*) [Field K] [CharZero K]

theorem transformedOrigin_inverse (g : Matrix.symplecticGroup (Fin 3) K) :
    transformedOrigin K g⁻¹ = positivePoint K (MukaiConormalOriginFrame.zeroPoint K) g := by
  rw [transformedOrigin,transpose_inv,primitiveAction_inv,LinearEquiv.symm_symm,
    positivePoint_origin]

theorem primitiveCubic_translated_origin (g : Matrix.symplecticGroup (Fin 3) K)
    (c : K) (S : Symmetric3 K) :
    MukaiPrimitiveQuartic.primitiveCubic K
      (formsAction K g⁻¹ (MukaiConormalPrimitive.conormalForm K (c,S)))
      (formsAction K g⁻¹ (MukaiConormalPrimitive.conormalForm K (c,S)))
      (formsAction K g⁻¹ (MukaiConormalPrimitive.conormalForm K (c,S))) =
      (4*S.val.det) • Module.Dual.eval K (Primitive K)
        (positivePoint K (MukaiConormalOriginFrame.zeroPoint K) g) := by
  rw [primitiveCubic_transformed_conormalForm,transformedOrigin_inverse]

end M9Native.MukaiCubicPositivePoint
