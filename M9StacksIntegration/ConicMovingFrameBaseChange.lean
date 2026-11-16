module

public import M9StacksIntegration.ConicPairMovingFrames

/-! Literal coefficient naturality of the actual head, tail and compensated
moving matrices over arbitrary complex field extensions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Matrix
open scoped Classical

namespace M9Native.ConicMovingFrameBaseChange

open M9.GraphBundleDescent M9.MovingDeterminantFrames
open GenericConicHead ConicFrameHeadMatrices MovingConicCells MovingConicTensorCoordinates

variable {K T : Type*} [Field K] [Field T] [Algebra ℂ K] [Algebra ℂ T]

theorem headMatrix_map (φ : K →ₐ[ℂ] T) (F : GL3 K) :
    (headMatrix K F).map φ.toRingHom =
      headMatrix T (Matrix.GeneralLinearGroup.map φ.toRingHom F) := by
  calc
    (headMatrix K F).map φ.toRingHom = (literalHead F.val).map φ.toRingHom :=
      congrArg (fun M => M.map φ.toRingHom) (headMatrix_eq_coefficients K F)
    _ = literalHead (F.val.map φ.toRingHom) := literalHead_map φ F.val
    _ = _ := (headMatrix_eq_coefficients T (Matrix.GeneralLinearGroup.map φ.toRingHom F)).symm

theorem tailMatrix_map (φ : K →ₐ[ℂ] T) (F : GL3 K) :
    (tailMatrix K F).map φ.toRingHom =
      tailMatrix T (Matrix.GeneralLinearGroup.map φ.toRingHom F) := by
  calc
    (tailMatrix K F).map φ.toRingHom = (literalTail F.val).map φ.toRingHom :=
      congrArg (fun M => M.map φ.toRingHom) (tailMatrix_eq_coefficients K F)
    _ = literalTail (F.val.map φ.toRingHom) := literalTail_map φ F.val
    _ = _ := (tailMatrix_eq_coefficients T (Matrix.GeneralLinearGroup.map φ.toRingHom F)).symm

theorem mappedHeadCondition (φ : K →ₐ[ℂ] T) (F : GL3 K)
    (hR : IsUnit (headMatrix K F).det) :
    IsUnit (headMatrix T (Matrix.GeneralLinearGroup.map φ.toRingHom F)).det := by
  have hd : φ ((headMatrix K F).det) =
      (headMatrix T (Matrix.GeneralLinearGroup.map φ.toRingHom F)).det :=
    (φ.map_det _).trans (congrArg Matrix.det (headMatrix_map φ F))
  exact hd ▸ hR.map φ.toRingHom

theorem headUnit_map (φ : K →ₐ[ℂ] T) (F : GL3 K)
    (hR : IsUnit (headMatrix K F).det) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (headUnit K F hR) =
      headUnit T (Matrix.GeneralLinearGroup.map φ.toRingHom F) (mappedHeadCondition φ F hR) := by
  apply Units.ext
  exact headMatrix_map φ F

theorem compensatedHead_map (φ : K →ₐ[ℂ] T) (F : GL3 K)
    (hR : IsUnit (headMatrix K F).det) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (compensatedHead K F hR) =
      compensatedHead T (Matrix.GeneralLinearGroup.map φ.toRingHom F)
        (mappedHeadCondition φ F hR) := by
  change Matrix.GeneralLinearGroup.map φ.toRingHom
      (Matrix.GeneralLinearGroup.scalar (Fin 4) ((Matrix.GeneralLinearGroup.det F)^2) *
        adjustedFrameHom K (headUnit K F hR)) =
    Matrix.GeneralLinearGroup.scalar (Fin 4)
        ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ.toRingHom F))^2) *
      adjustedFrameHom T
        (headUnit T (Matrix.GeneralLinearGroup.map φ.toRingHom F) (mappedHeadCondition φ F hR))
  rw [map_mul, Matrix.GeneralLinearGroup.map_scalar, map_pow,
    ConicPairMovingFrames.adjustedFrame_map, headUnit_map, Matrix.GeneralLinearGroup.map_det]

theorem movingCellMatrix_map (φ : K →ₐ[ℂ] T) (F : GL3 K)
    (hR : IsUnit (headMatrix K F).det) :
    (movingCellMatrix K F hR).map φ.toRingHom =
      movingCellMatrix T (Matrix.GeneralLinearGroup.map φ.toRingHom F)
        (mappedHeadCondition φ F hR) := by
  have hi : (headUnit K F hR)⁻¹.val.map φ.toRingHom =
      (headUnit T (Matrix.GeneralLinearGroup.map φ.toRingHom F)
        (mappedHeadCondition φ F hR))⁻¹.val :=
    (congrArg Units.val ((Matrix.GeneralLinearGroup.map φ.toRingHom).map_inv (headUnit K F hR))).trans
      (congrArg (fun g : GL4 T => g⁻¹.val) (headUnit_map φ F hR))
  change (tailMatrix K F * (headUnit K F hR)⁻¹.val).map φ.toRingHom = _
  rw [Matrix.map_mul, tailMatrix_map, hi]
  rfl

end M9Native.ConicMovingFrameBaseChange
