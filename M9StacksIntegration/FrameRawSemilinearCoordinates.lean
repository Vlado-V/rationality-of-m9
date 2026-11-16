module

public import M9StacksIntegration.ConicRawGammaMatrices
public import M9.FrameHomFieldDescent

/-! Matrix coordinates of the actual coefficient-semilinear tensor action.
The complex Gamma matrices are fixed constants; the original ambient-field
automorphism remains on every vector coefficient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open scoped TensorProduct
namespace M9Native.FrameRawSemilinearCoordinates
open M9.FrameBundleDescent M9.FrameBundleDescent.Standard
open M9.DeterminantFrameScalarExtension M9.StandardFourPlaneRepresentation
open M9.DeterminantFrameScalarEquivariance (rawGamma)
open ConicRawGammaMatrices

local instance ambientEvenAction : MulSemiringAction Even Ambient :=
  M9.FrameQuadraticExtension.evenAction
local instance ambientEvenCommutes : SMulCommClass Even ℂ Ambient where
  smul_comm g c x :=
    map_smul (M9.FrameQuadraticExtension.evenRepresentation g).toLinearEquiv c x

theorem smul_complex (g : Even) (c : ℂ) :
    g • algebraMap ℂ Ambient c = algebraMap ℂ Ambient c :=
  (M9.FrameQuadraticExtension.evenRepresentation g).commutes c

theorem gammaK_entry_fixed (g : Even) (a : M9.FrameBundleDescent.Gamma) (i j : Fin 4) :
    g • (gammaK Ambient a).val i j = (gammaK Ambient a).val i j :=
  smul_complex g ((gammaC a).val i j)

def coefficientOperator (g : Even) :
    (Ambient ⊗[ℂ] M9.StandardFourPlaneRepresentation.E0) →ₗ[ℂ]
      (Ambient ⊗[ℂ] M9.StandardFourPlaneRepresentation.E0) :=
  TensorProduct.map (MulSemiringAction.toAlgAut Even ℂ Ambient g).toLinearMap LinearMap.id

theorem rawCoordinates_coefficientOperator (g : Even)
    (x : Ambient ⊗[ℂ] M9.StandardFourPlaneRepresentation.E0) :
    rawCoordinates Ambient (coefficientOperator g x) =
      fun i => g • rawCoordinates Ambient x i := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      funext i
      change algebraMap ℂ Ambient (tensorEvaluationEquiv x i) * (g • a) =
        g • (algebraMap ℂ Ambient (tensorEvaluationEquiv x i) * a)
      rw [smul_mul', smul_complex]
  | add x y hx hy =>
      funext i
      simp only [map_add, hx, hy, Pi.add_apply, smul_add]

theorem actualRaw_smul_eq_gamma_coefficient (side : Bool) (g : Even) (x : ActualRaw side) :
    g • x = rawGamma Ambient (sideFactor side g) (coefficientOperator g x) := by
  change Ambient ⊗[ℂ] M9.StandardFourPlaneRepresentation.E0 at x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      change (g • a) ⊗ₜ[ℂ] tensorRepresentation (sideFactor side g) x =
        rawGamma Ambient (sideFactor side g) ((g • a) ⊗ₜ[ℂ] x)
      exact (LinearEquiv.baseChange_tmul ℂ Ambient
        M9.StandardFourPlaneRepresentation.E0 M9.StandardFourPlaneRepresentation.E0
        (e := tensorRepresentation (sideFactor side g)) (g • a) x).symm
  | add x y hx hy =>
      simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy

theorem rawCoordinates_smul (side : Bool) (g : Even) (x : ActualRaw side) :
    rawCoordinates Ambient (g • x) =
      (gammaK Ambient (sideFactor side g)).val.mulVec
        (fun i => g • rawCoordinates Ambient x i) := by
  exact (congrArg (rawCoordinates Ambient)
    (actualRaw_smul_eq_gamma_coefficient side g x)).trans
      ((gammaK_mulVec_rawCoordinates Ambient (sideFactor side g) (coefficientOperator g x)).symm.trans
        (congrArg (gammaK Ambient (sideFactor side g)).val.mulVec
          (rawCoordinates_coefficientOperator g x)))

theorem rawCoordinates_inv_smul_cancel (side : Bool) (g : Even)
    (x : ActualRaw side) (i : Fin 4) :
    g • rawCoordinates Ambient (g⁻¹ • x) i =
      ∑ a : Fin 4, (gammaK Ambient (sideFactor side g⁻¹)).val i a *
        rawCoordinates Ambient x a := by
  rw [rawCoordinates_smul]
  simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul',
    gammaK_entry_fixed, smul_inv_smul]

end M9Native.FrameRawSemilinearCoordinates
end
