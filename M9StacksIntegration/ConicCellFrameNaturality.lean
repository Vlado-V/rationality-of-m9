module

public import M9StacksIntegration.MovingConicTensorCoordinates

/-! Actual moving cell frames depend only on the embedded plane. This
gives literal deck and scalar transition formulas for the original
determinant-compensated raw frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open scoped TensorProduct

namespace M9Native.ConicCellFrameNaturality

open M9.GraphBundleDescent M9.StandardFourPlaneRepresentation
open M9.MovingDeterminantFrames M9.DeterminantFrameScalarExtension
open M9.DeterminantFrameScalarEquivariance M9.MovingScalarExtendedGraphFrames
open ConicCompatibleGraphCoordinates ConicFrameHeadMatrices MovingConicCells
open MovingConicTensorCoordinates

variable (K : Type*) [Field K] [Algebra ℂ K]

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }
local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

def cellHead (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    movingPlane K (standardPlane K) F ≃ₗ[K] Head K :=
  (movingCellFrame K F hR).symm.trans (standardPlaneBasis K).equivFun

theorem cellHead_apply (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (q : movingPlane K (standardPlane K) F) :
    cellHead K F hR q = (conicSplit K q.val).1 := by
  let e := movingCellFrame K F hR
  have h := congrArg Prod.fst (movingCellFrame_coordinates K F hR (e.symm q))
  exact h.symm.trans (congrArg (fun v : movingPlane K (standardPlane K) F =>
    (conicSplit K v.val).1) (e.apply_symm_apply q))

theorem cellFrame_natural (F G : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hG : IsUnit (headMatrix K G).det)
    (h : movingPlane K (standardPlane K) F = movingPlane K (standardPlane K) G) :
    (movingCellFrame K F hF).trans (planeEquivOfEq K h) = movingCellFrame K G hG := by
  apply LinearEquiv.ext
  intro q
  apply (cellHead K G hG).injective
  calc
    cellHead K G hG (planeEquivOfEq K h (movingCellFrame K F hF q)) =
        (conicSplit K (movingCellFrame K F hF q).val).1 :=
      cellHead_apply K G hG _
    _ = (standardPlaneBasis K).equivFun q :=
      congrArg Prod.fst (movingCellFrame_coordinates K F hF q)
    _ = cellHead K G hG (movingCellFrame K G hG q) :=
      (congrArg (standardPlaneBasis K).equivFun
        ((movingCellFrame K G hG).symm_apply_apply q)).symm

theorem cellTensorCoordinates_natural (F G : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hG : IsUnit (headMatrix K G).det)
    (h : movingPlane K (standardPlane K) F = movingPlane K (standardPlane K) G)
    (x : Twisted K (movingPlane K (standardPlane K) F)) :
    cellTensorCoordinates K G hG (tensorTransport (planeEquivOfEq K h) x) =
      cellTensorCoordinates K F hF x := by
  let p := tensorTransport (movingCellFrame K F hF)
  let q := tensorTransport (movingCellFrame K G hG)
  let j := tensorTransport (planeEquivOfEq K h)
  have ht : p.trans j = q :=
    (tensorTransport_trans (movingCellFrame K F hF) (planeEquivOfEq K h)).symm.trans
      (congrArg tensorTransport (cellFrame_natural K F G hF hG h))
  obtain ⟨z,rfl⟩ := p.surjective x
  have hz : j (p z) = q z := LinearEquiv.congr_fun ht z
  calc
    cellTensorCoordinates K G hG (j (p z)) = cellTensorCoordinates K G hG (q z) :=
      congrArg (cellTensorCoordinates K G hG) hz
    _ = twistedCoordinates K z :=
      congrArg (twistedCoordinates K) (q.symm_apply_apply z)
    _ = cellTensorCoordinates K F hF (p z) :=
      (congrArg (twistedCoordinates K) (p.symm_apply_apply z)).symm

/-- Actual raw-frame transition through equality of actual embedded planes. -/
theorem compensatedHead_transition (F G : GL3 K)
    (hF : IsUnit (headMatrix K F).det) (hG : IsUnit (headMatrix K G).det)
    (h : movingPlane K (standardPlane K) G = movingPlane K (standardPlane K) F)
    (a : (K ⊗[ℂ] E0) ≃ₗ[K] (K ⊗[ℂ] E0))
    (ha : (rawMovingFrame K G).trans (tensorTransport (planeEquivOfEq K h)) =
      a.trans (rawMovingFrame K F)) (x : K ⊗[ℂ] E0) :
    (compensatedHead K G hG).val.mulVec (rawCoordinates K x) =
      (compensatedHead K F hF).val.mulVec (rawCoordinates K (a x)) := by
  have hx := LinearEquiv.congr_fun ha x
  calc
    (compensatedHead K G hG).val.mulVec (rawCoordinates K x) =
        cellTensorCoordinates K G hG (rawMovingFrame K G x) :=
      (rawMovingFrame_coordinates K G hG x).symm
    _ = cellTensorCoordinates K F hF
        (tensorTransport (planeEquivOfEq K h) (rawMovingFrame K G x)) :=
      (cellTensorCoordinates_natural K G F hG hF h _).symm
    _ = cellTensorCoordinates K F hF (rawMovingFrame K F (a x)) :=
      congrArg (cellTensorCoordinates K F hF) hx
    _ = _ := rawMovingFrame_coordinates K F hF (a x)

theorem compensatedHead_right_gamma (a : M9.TetrahedralGroup.Gamma) (F : GL3 K)
    (hF : IsUnit (headMatrix K F).det)
    (hG : IsUnit (headMatrix K (F * constantGamma K a)).det) (x : K ⊗[ℂ] E0) :
    (compensatedHead K (F * constantGamma K a) hG).val.mulVec (rawCoordinates K x) =
      (compensatedHead K F hF).val.mulVec (rawCoordinates K (rawGamma K a x)) :=
  compensatedHead_transition K F (F * constantGamma K a) hF hG
    (movingPlane_right K (standardPlane K) (constantGamma K a) F (constantGamma_plane K a))
    (rawGamma K a) (rawMovingFrame_right_gamma K a F) x

/-- The genuine compensator removes arbitrary projective rescaling. -/
theorem compensatedHead_scalar (a : Kˣ) (F : GL3 K)
    (hF : IsUnit (headMatrix K F).det)
    (hG : IsUnit (headMatrix K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F)).det) :
    compensatedHead K (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) hG =
      compensatedHead K F hF := by
  apply (matrixLinearEquiv K).injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := (rawCoordinates K).surjective v
  exact compensatedHead_transition K F (Matrix.GeneralLinearGroup.scalar (Fin 3) a * F) hF hG
    (movingPlane_scalar K (standardPlane K) a F) (LinearEquiv.refl K _) (rawMovingFrame_scalar K a F) x

end M9Native.ConicCellFrameNaturality
