module

public import M9StacksIntegration.MukaiPrimitiveSymplectic
public import M9StacksIntegration.PrimitiveCoefficientAction

/-! Exact comparison of the exterior quotient action and the native primitive transpose action. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiPrimitiveQuarticAction

open LagrangianField LagrangianTransitivity LagrangianSigmaInvariance
open MukaiPrimitiveProjector MukaiPrimitiveQuartic MukaiConormalPrimitive
open PrimitiveCoefficientAction MukaiPrimitiveSymplectic

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
theorem symplecticEquiv_toLinearMap (g : Matrix.symplecticGroup (Fin 3) K) :
    (symplecticEquiv K g).toLinearMap = (matrixSix K g).mulVecLin := by
  apply LinearMap.ext
  intro v
  exact symplecticEquiv_apply K g v

theorem quotientMap_eq_dualMap_transpose (g : Matrix.symplecticGroup (Fin 3) K) :
    quotientMap K (matrixSix K g).mulVecLin =
      (primitiveAction K (transposeSymplectic K g)).dualMap.toLinearMap := by
  apply LinearMap.ext
  intro ell
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  have hs := symplecticEquiv_preserves_sigma K g
  rw [symplecticEquiv_toLinearMap] at hs
  rw [quotientMap_primitiveClass K (matrixSix K g).mulVecLin hs]
  exact restriction_transpose K g w

theorem primitiveCubic_nativeAction (g : Matrix.symplecticGroup (Fin 3) K)
    (u v w t : Forms K) :
    primitiveCubic K ((primitiveAction K (transposeSymplectic K g)).dualMap u)
      ((primitiveAction K (transposeSymplectic K g)).dualMap v)
      ((primitiveAction K (transposeSymplectic K g)).dualMap w)
      ((primitiveAction K (transposeSymplectic K g)).dualMap t) =
      primitiveCubic K u v w t := by
  have h := primitiveCubic_invariant K g u v w t
  rw [symplecticEquiv_toLinearMap] at h
  simpa only [quotientMap_eq_dualMap_transpose, LinearEquiv.coe_coe] using h

end M9Native.MukaiPrimitiveQuarticAction
