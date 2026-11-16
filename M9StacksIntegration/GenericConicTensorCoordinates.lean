module

public import M9StacksIntegration.MovingConicTensorCoordinates

/-! The actual compensated moving frame at the actual normalized generic
conic frame. Its head invertibility is proved, rather than a hypothesis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open scoped TensorProduct

namespace M9Native.GenericConicTensorCoordinates

open GenericConicHead ConicFrameHeadMatrices MovingConicCells MovingConicTensorCoordinates
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open M9.StandardFourPlaneRepresentation

theorem headCondition : IsUnit (headMatrix L genericFrameUnit).det := by
  rw [genericHead_actual]
  exact isUnit_iff_ne_zero.mpr genericHead_det_ne_zero

theorem headUnit_eq : headUnit L genericFrameUnit headCondition = genericHeadUnit := by
  apply Units.ext
  exact genericHead_actual

theorem cellMatrix_eq : movingCellMatrix L genericFrameUnit headCondition = genericPlaneMatrix := by
  rw [movingCellMatrix, genericTail_actual, headUnit_eq]
  rfl

theorem compensatedHead_eq :
    compensatedHead L genericFrameUnit headCondition = genericCompensatedFrame := by
  rw [compensatedHead, headUnit_eq]
  rfl

/-- Exact generic moving tensor coefficients, with no invertibility premise. -/
theorem actual_rawMovingFrame_coordinates (x : L ⊗[ℂ] E0) :
    cellTensorCoordinates L genericFrameUnit headCondition (rawMovingFrame L genericFrameUnit x) =
      genericCompensatedFrame.val.mulVec (rawCoordinates L x) := by
  exact (rawMovingFrame_coordinates L genericFrameUnit headCondition x).trans
    (congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4) L => g.val.mulVec (rawCoordinates L x))
      compensatedHead_eq)

end M9Native.GenericConicTensorCoordinates
