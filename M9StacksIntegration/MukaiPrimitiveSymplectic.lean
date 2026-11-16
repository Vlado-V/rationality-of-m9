module

public import M9StacksIntegration.MukaiPrimitiveQuartic

/-!
# Actual symplectic invariance of the native primitive quartic and cubic

The determinant is computed on the literal six-coordinate symplectic
equivalence. The quotient map is the actual exterior-induced quotient
map of the preceding leaf.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiPrimitiveSymplectic

open LagrangianField LagrangianTransitivity LagrangianSigmaInvariance
open MukaiPrimitiveQuartic

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
theorem det_symplecticEquiv (g : Matrix.symplecticGroup (Fin 3) K) :
    LinearMap.det (symplecticEquiv K g).toLinearMap = 1 := by
  change LinearMap.det (matrixSix K g).mulVecLin = 1
  rw [← LinearMap.det_toMatrix (Pi.basisFun K (Fin 6))]
  have h : LinearMap.toMatrix (Pi.basisFun K (Fin 6)) (Pi.basisFun K (Fin 6))
      (matrixSix K g).mulVecLin = matrixSix K g := by
    ext i j
    simp
  rw [h, matrixSix_det_eq_one]

omit [CharZero K] in
theorem preserves_omega (g : Matrix.symplecticGroup (Fin 3) K) (v w : V K) :
    omega K (symplecticEquiv K g v) (symplecticEquiv K g w) = omega K v w :=
  symplecticEquiv_preserves_omega K g v w

theorem primitiveQuartic_invariant (g : Matrix.symplecticGroup (Fin 3) K) (ell : Forms K) :
    primitiveQuartic K (quotientMap K (symplecticEquiv K g).toLinearMap ell) =
      primitiveQuartic K ell := by
  rw [primitiveQuartic_covariance K (symplecticEquiv K g) (preserves_omega K g)
    (symplecticEquiv_preserves_sigma K g), det_symplecticEquiv]
  simp

theorem primitiveCubic_invariant (g : Matrix.symplecticGroup (Fin 3) K) (u v w t : Forms K) :
    primitiveCubic K (quotientMap K (symplecticEquiv K g).toLinearMap u)
      (quotientMap K (symplecticEquiv K g).toLinearMap v)
      (quotientMap K (symplecticEquiv K g).toLinearMap w)
      (quotientMap K (symplecticEquiv K g).toLinearMap t) = primitiveCubic K u v w t := by
  rw [primitiveCubic_covariance K (symplecticEquiv K g) (preserves_omega K g)
    (symplecticEquiv_preserves_sigma K g), det_symplecticEquiv]
  simp

end M9Native.MukaiPrimitiveSymplectic
