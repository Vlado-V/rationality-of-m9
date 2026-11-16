module

public import M9StacksIntegration.GenericConicBaseCoordinates
public import M9StacksIntegration.PairProjectiveEquivariance
public import M9StacksIntegration.ConicTensorIsomCoordinates

/-! Actual two independent moving frames over the original projective
frame-pair field. All four-by-four and base matrices are literal coefficient
extensions of the actual normalized conic-frame construction. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Matrix
open scoped Classical

namespace M9Native.ConicPairMovingFrames

open M9.GraphBundleDescent GenericConicHead
open ConicFrameHeadMatrices MovingConicCells MovingConicTensorCoordinates

abbrev B := ConicGraphBaseCoordinates.FrameField

def firstEmbedding : L →ₐ[ℂ] B :=
  PairProjectiveRatios.pairProjectiveEquiv.toAlgHom.comp
    ConicFrameIndependentPairAction.coefficientEmbedding

def secondEmbedding : L →ₐ[ℂ] B :=
  PairProjectiveRatios.pairProjectiveEquiv.toAlgHom.comp
    ConicFrameIndependentPairAction.outerEmbedding

def blockEmbedding : Fin 2 → (L →ₐ[ℂ] B) := ![firstEmbedding,secondEmbedding]

def frameUnit (s : Fin 2) : Matrix.GeneralLinearGroup (Fin 3) B :=
  Matrix.GeneralLinearGroup.map (blockEmbedding s).toRingHom genericFrameUnit

def movingHeadUnit (s : Fin 2) : GL4 B :=
  Matrix.GeneralLinearGroup.map (blockEmbedding s).toRingHom genericHeadUnit

def compensatedFrame (s : Fin 2) : GL4 B :=
  Matrix.GeneralLinearGroup.map (blockEmbedding s).toRingHom genericCompensatedFrame

def planeMatrix (s : Fin 2) : BaseMatrix B :=
  genericPlaneMatrix.map (blockEmbedding s).toRingHom

theorem headMatrix_eq_mapped (s : Fin 2) :
    headMatrix B (frameUnit s) = genericHead.map (blockEmbedding s).toRingHom := by
  rw [headMatrix_eq_coefficients]
  have h := literalHead_map (blockEmbedding s) genericFrameUnit.val
  change genericHead.map (blockEmbedding s).toRingHom = headCoefficients B (frameUnit s) at h
  exact h.symm

theorem tailMatrix_eq_mapped (s : Fin 2) :
    tailMatrix B (frameUnit s) = genericTail.map (blockEmbedding s).toRingHom := by
  rw [tailMatrix_eq_coefficients]
  have h := literalTail_map (blockEmbedding s) genericFrameUnit.val
  change genericTail.map (blockEmbedding s).toRingHom = tailCoefficients B (frameUnit s) at h
  exact h.symm

theorem headCondition (s : Fin 2) : IsUnit (headMatrix B (frameUnit s)).det := by
  rw [headMatrix_eq_mapped]
  exact (Matrix.GeneralLinearGroup.det (movingHeadUnit s)).isUnit

theorem actualHeadUnit (s : Fin 2) :
    headUnit B (frameUnit s) (headCondition s) = movingHeadUnit s := by
  apply Units.ext
  exact headMatrix_eq_mapped s

section Naturality
variable {K T : Type*} [Field K] [Field T]

theorem adjustedFrame_map (φ : K →+* T) (g : GL4 K) :
    Matrix.GeneralLinearGroup.map φ (adjustedFrameHom K g) =
      adjustedFrameHom T (Matrix.GeneralLinearGroup.map φ g) := by
  change Matrix.GeneralLinearGroup.map φ
    (Matrix.GeneralLinearGroup.scalar (Fin 4) (Matrix.GeneralLinearGroup.det g)⁻¹ * g) =
      Matrix.GeneralLinearGroup.scalar (Fin 4)
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g))⁻¹ *
        Matrix.GeneralLinearGroup.map φ g
  rw [map_mul, Matrix.GeneralLinearGroup.map_scalar, Matrix.GeneralLinearGroup.map_det, map_inv]

end Naturality

theorem actualCompensatedFrame (s : Fin 2) :
    compensatedHead B (frameUnit s) (headCondition s) = compensatedFrame s := by
  rw [compensatedHead, actualHeadUnit]
  simp only [compensatedFrame, genericCompensatedFrame, map_mul,
    Matrix.GeneralLinearGroup.map_scalar, map_pow, adjustedFrame_map,
    frameUnit, movingHeadUnit, Matrix.GeneralLinearGroup.map_det]

theorem actualPlaneMatrix (s : Fin 2) :
    movingCellMatrix B (frameUnit s) (headCondition s) = planeMatrix s := by
  rw [movingCellMatrix, tailMatrix_eq_mapped, actualHeadUnit]
  change genericTail.map (blockEmbedding s).toRingHom *
      (Matrix.GeneralLinearGroup.map (blockEmbedding s).toRingHom genericHeadUnit)⁻¹.val =
    (genericTail * genericHeadUnit⁻¹.val).map (blockEmbedding s).toRingHom
  have hi := congrArg Units.val
    ((Matrix.GeneralLinearGroup.map (blockEmbedding s).toRingHom).map_inv genericHeadUnit)
  rw [← hi, Matrix.map_mul]
  rfl

end M9Native.ConicPairMovingFrames
