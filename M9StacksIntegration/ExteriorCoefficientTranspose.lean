module

public import M9StacksIntegration.MukaiPrimitiveDuality

/-!
# Transpose naturality of the actual exterior coefficient duality

This is the literal dot-duality in the original twenty exterior
coordinates.  For an arbitrary six-by-six matrix its transpose is the
adjoint after taking third exterior powers.  No invertibility or
symplectic invariance hypothesis is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module

universe u

namespace M9Native.ExteriorCoefficientTranspose

open LagrangianField MukaiPrimitiveDuality

variable (K : Type u) [Field K]

theorem coefficientDuality_symmetric (w z : Third K) :
    coefficientDuality K w z = coefficientDuality K z w := by
  have h : (coefficientDuality K).toLinearMap.flip =
      (coefficientDuality K).toLinearMap := by
    apply (thirdBasis20 K).ext
    intro i
    apply (thirdBasis20 K).ext
    intro j
    simp [coefficientDuality, Basis.toDual_apply, eq_comm]
  exact LinearMap.congr_fun (LinearMap.congr_fun h z) w

/-- The actual coefficient is the corresponding literal matrix minor. -/
theorem coefficientDuality_map_basis (A : Matrix (Fin 6) (Fin 6) K) (i j : Fin 20) :
    coefficientDuality K (exteriorPower.map 3 A.mulVecLin (thirdBasis20 K i))
        (thirdBasis20 K j) =
      Matrix.det (fun a b : Fin 3 =>
        A (LagrangianRing.triple j a) (LagrangianRing.triple i b)) := by
  rw [coefficientDuality, Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change (thirdBasis20 K).coord j
    (exteriorPower.map 3 A.mulVecLin (thirdBasis20 K i)) = _
  rw [← LagrangianPluckerLinear.coordinate3_triple K j]
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply,
    exteriorPower.map_apply_ιMulti]
  simp only [coordinate3, exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [← Matrix.det_transpose (fun a b : Fin 3 =>
    A (LagrangianRing.triple j a) (LagrangianRing.triple i b))]
  congr 1
  ext a b
  simp [LagrangianRing.basisVector, LinearMap.proj_apply, Matrix.transpose_apply]

/-- Taking the third exterior power respects the original coefficient
adjoint, for arbitrary matrices. -/
theorem coefficientDuality_exteriorPower_transpose_linear
    (A : Matrix (Fin 6) (Fin 6) K) :
    (coefficientDuality K).toLinearMap.comp (exteriorPower.map 3 A.mulVecLin) =
      (exteriorPower.map 3 A.transpose.mulVecLin).dualMap.comp
        (coefficientDuality K).toLinearMap := by
  apply (thirdBasis20 K).ext
  intro i
  apply (thirdBasis20 K).ext
  intro j
  change coefficientDuality K (exteriorPower.map 3 A.mulVecLin (thirdBasis20 K i))
      (thirdBasis20 K j) =
    coefficientDuality K (thirdBasis20 K i)
      (exteriorPower.map 3 A.transpose.mulVecLin (thirdBasis20 K j))
  rw [coefficientDuality_symmetric K (thirdBasis20 K i),
    coefficientDuality_map_basis, coefficientDuality_map_basis]
  refine (Matrix.det_transpose (fun a b : Fin 3 =>
    A (LagrangianRing.triple j a) (LagrangianRing.triple i b))).symm.trans ?_
  congr 1

theorem coefficientDuality_exteriorPower_transpose
    (A : Matrix (Fin 6) (Fin 6) K) (w z : Third K) :
    coefficientDuality K (exteriorPower.map 3 A.mulVecLin w) z =
      coefficientDuality K w (exteriorPower.map 3 A.transpose.mulVecLin z) :=
  LinearMap.congr_fun
    (LinearMap.congr_fun (coefficientDuality_exteriorPower_transpose_linear K A) w) z

end M9Native.ExteriorCoefficientTranspose
