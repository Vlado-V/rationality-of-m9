module

public import M9StacksIntegration.MovingConicTensorCoordinates

/-! The actual trace-dual moving plane has the same compensated coordinate
matrix. The trace pairing, not a replacement second representation, supplies
the comparison. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

open scoped TensorProduct

namespace M9Native.DualConicTensorCoordinates

open M9.GraphBundleDescent M9.StandardFourPlaneRepresentation
open M9.MovingDeterminantFrames M9.MovingDualDeterminantFrames
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open M9.MovingScalarExtendedGraphFrames
open ConicFrameHeadMatrices MovingConicCells MovingConicTensorCoordinates

variable (K : Type*) [Field K] [Algebra ℂ K] [CharZero K]

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }
local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }
local instance dualPlaneGroup (S : Submodule K (Module.Dual K (M9.Symmetric3 K))) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def dualCellTensorCoordinates (H : GL3 K) (hR : IsUnit (headMatrix K H).det) :
    Twisted K (dualMovingPlane K (standardPlane K) H) ≃ₗ[K] Head K :=
  (tensorTransport (tracePlaneFrame K (standardPlane K) H)).symm.trans
    (cellTensorCoordinates K H hR)

theorem rawDualMovingFrame_coordinates (H : GL3 K) (hR : IsUnit (headMatrix K H).det)
    (x : K ⊗[ℂ] E0) :
    dualCellTensorCoordinates K H hR (rawDualMovingFrame K H x) =
      (compensatedHead K H hR).val.mulVec (rawCoordinates K x) := by
  let t := tensorTransport (tracePlaneFrame K (standardPlane K) H)
  calc
    dualCellTensorCoordinates K H hR (rawDualMovingFrame K H x) =
        cellTensorCoordinates K H hR (t.symm (t (rawMovingFrame K H x))) := rfl
    _ = cellTensorCoordinates K H hR (rawMovingFrame K H x) :=
      congrArg (cellTensorCoordinates K H hR) (t.symm_apply_apply (rawMovingFrame K H x))
    _ = _ := rawMovingFrame_coordinates K H hR x

omit [CharZero K] in
theorem sourceFrame_coordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    (rawMovingFrame K F).trans (cellTensorCoordinates K F hR) =
      (rawCoordinates K).trans (matrixLinearEquiv K (compensatedHead K F hR)) := by
  apply LinearEquiv.ext
  exact rawMovingFrame_coordinates K F hR

theorem targetFrame_coordinates (H : GL3 K) (hR : IsUnit (headMatrix K H).det) :
    (rawDualMovingFrame K H).trans (dualCellTensorCoordinates K H hR) =
      (rawCoordinates K).trans (matrixLinearEquiv K (compensatedHead K H hR)) := by
  apply LinearEquiv.ext
  exact rawDualMovingFrame_coordinates K H hR

end M9Native.DualConicTensorCoordinates
