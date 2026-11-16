module

public import M9StacksIntegration.ConicMovingFrameBaseChange
public import M9StacksIntegration.ConicMovingFrameScalar
public import M9StacksIntegration.ConicFrameGammaInvariant

/-! Literal right-deck naturality of the actual normalized generic
determinant-compensated frame. The normalization scalar and both head
minors are proved, not supplied as action or rank hypotheses. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

open scoped Classical TensorProduct

namespace M9Native.GenericConicCompensatorGamma

open M9.GraphBundleDescent M9.MovingDeterminantFrames M9.StandardFourPlaneRepresentation
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open GenericConicHead GenericConicTensorCoordinates ConicMovingFrameBaseChange
open MovingConicTensorCoordinates ConicCellFrameNaturality ConicMovingFrameScalar

abbrev Gamma := M9.TetrahedralGroup.Gamma

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

def normalizationUnit (g : Gamma) : Lˣ :=
  Units.mk0 (ConicFrameGammaInvariant.rightFrame g 0 0)⁻¹
    (inv_ne_zero (ConicFrameGammaInvariant.rightFrame_firstRow g 0))

def rightUnit (g : Gamma) : GL3 L := genericFrameUnit * constantGamma L g

theorem frame_image (g : Gamma) :
    Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom genericFrameUnit =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit g) * rightUnit g := by
  apply Units.ext
  calc
    (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
        genericFrameUnit).val =
        ConicFrameRationalGamma.genericFrame.map
          (ConicFrameRationalGamma.rationalRepresentation g).toRingHom := rfl
    _ = (ConicFrameGammaInvariant.rightFrame g 0 0)⁻¹ • ConicFrameGammaInvariant.rightFrame g :=
      ConicFrameGammaInvariant.genericFrame_image g
    _ = _ := (scalar_frame_value L (normalizationUnit g) (rightUnit g)).symm

theorem rightHeadCondition (g : Gamma) : IsUnit (ConicFrameHeadMatrices.headMatrix L (rightUnit g)).det := by
  have h := mappedHeadCondition (ConicFrameRationalGamma.rationalRepresentation g).toAlgHom
    genericFrameUnit GenericConicTensorCoordinates.headCondition
  change IsUnit (ConicFrameHeadMatrices.headMatrix L
    (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
      genericFrameUnit)).det at h
  rw [frame_image] at h
  exact (headCondition_scalar_iff L (normalizationUnit g) (rightUnit g)).mp h

theorem scaledHeadCondition (g : Gamma) :
    IsUnit (ConicFrameHeadMatrices.headMatrix L
      (Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit g) * rightUnit g)).det :=
  (headCondition_scalar_iff L (normalizationUnit g) (rightUnit g)).mpr (rightHeadCondition g)

theorem compensatedHead_congr {K : Type*} [Field K] [Algebra ℂ K] {F G : GL3 K}
    (h : F = G) (hF : IsUnit (ConicFrameHeadMatrices.headMatrix K F).det)
    (hG : IsUnit (ConicFrameHeadMatrices.headMatrix K G).det) :
    compensatedHead K F hF = compensatedHead K G hG := by
  cases h
  rfl

/-- The actual old field deck action translates the generic compensator
to the compensator of the actual unnormalised right frame. -/
theorem compensator_image (g : Gamma) :
    Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
      genericCompensatedFrame = compensatedHead L (rightUnit g) (rightHeadCondition g) := by
  calc
    Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
        genericCompensatedFrame =
        Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
          (compensatedHead L genericFrameUnit GenericConicTensorCoordinates.headCondition) :=
      congrArg (Matrix.GeneralLinearGroup.map
        (ConicFrameRationalGamma.rationalRepresentation g).toRingHom)
          GenericConicTensorCoordinates.compensatedHead_eq.symm
    _ = compensatedHead L
        (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom genericFrameUnit)
        (mappedHeadCondition (ConicFrameRationalGamma.rationalRepresentation g).toAlgHom
          genericFrameUnit GenericConicTensorCoordinates.headCondition) :=
      compensatedHead_map (ConicFrameRationalGamma.rationalRepresentation g).toAlgHom
        genericFrameUnit GenericConicTensorCoordinates.headCondition
    _ = compensatedHead L
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (normalizationUnit g) * rightUnit g)
        (scaledHeadCondition g) := compensatedHead_congr (frame_image g) _ _
    _ = _ := compensatedHead_scalar L (normalizationUnit g) (rightUnit g)
      (rightHeadCondition g) (scaledHeadCondition g)

/-- The literal coefficient-field action on β has the actual original
scalar-extended E₀ action on its right. -/
theorem compensator_image_action (g : Gamma) (x : L ⊗[ℂ] E0) :
    (Matrix.GeneralLinearGroup.map (ConicFrameRationalGamma.rationalRepresentation g).toRingHom
      genericCompensatedFrame).val.mulVec (rawCoordinates L x) =
        genericCompensatedFrame.val.mulVec (rawCoordinates L (rawGamma L g x)) := by
  calc
    _ = (compensatedHead L (rightUnit g) (rightHeadCondition g)).val.mulVec (rawCoordinates L x) :=
      congrArg (fun u : GL4 L => u.val.mulVec (rawCoordinates L x)) (compensator_image g)
    _ = (compensatedHead L genericFrameUnit GenericConicTensorCoordinates.headCondition).val.mulVec
        (rawCoordinates L (rawGamma L g x)) :=
      compensatedHead_right_gamma L g genericFrameUnit GenericConicTensorCoordinates.headCondition
        (rightHeadCondition g) x
    _ = _ := congrArg (fun u : GL4 L => u.val.mulVec (rawCoordinates L (rawGamma L g x)))
      GenericConicTensorCoordinates.compensatedHead_eq

end M9Native.GenericConicCompensatorGamma
