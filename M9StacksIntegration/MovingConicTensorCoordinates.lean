module

public import M9StacksIntegration.MovingConicCells
public import M9StacksIntegration.GenericConicHead
public import M9.MovingScalarExtendedGraphFrames

/-! Literal coordinates of the actual determinant-compensated moving frame
in the actual conic-compatible graph cell. The compensating matrix is
det(F)^2 det(R(F))⁻¹ R(F), obtained from actual exterior-dual transport. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

open scoped TensorProduct
open Matrix

namespace M9Native.MovingConicTensorCoordinates

open M9.GraphBundleDescent M9.StandardFourPlaneRepresentation
open M9.MovingDeterminantFrames M9.MovingDualDeterminantFrames
open M9.DeterminantFrameScalarExtension M9.DeterminantFrameScalarEquivariance
open ConicFrameHeadMatrices MovingConicCells

variable (K : Type*) [Field K] [Algebra ℂ K]

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

theorem standardEndo_coordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (q : standardPlane K) :
    (standardPlaneBasis K).equivFun (standardEndo K F hR q) =
      (headUnit K F hR).val.mulVec ((standardPlaneBasis K).equivFun q) := by
  change (standardPlaneBasis K).equivFun ((standardPlaneBasis K).equivFun.symm
    (headChange K F hR ((standardPlaneBasis K).equivFun q))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem headChange_det (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    LinearEquiv.det (headChange K F hR) = Matrix.GeneralLinearGroup.det (headUnit K F hR) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  exact determinantLine_character K (headUnit K F hR)

theorem standardEndo_det (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    LinearEquiv.det (standardEndo K F hR) = Matrix.GeneralLinearGroup.det (headUnit K F hR) := by
  let b := (standardPlaneBasis K).equivFun
  have he : standardEndo K F hR = (b.trans (headChange K F hR)).trans b.symm :=
    (LinearEquiv.trans_assoc b (headChange K F hR) b.symm).symm
  have hd : LinearEquiv.det ((b.trans (headChange K F hR)).trans b.symm) =
      LinearEquiv.det (headChange K F hR) := by
    simpa only [LinearEquiv.symm_symm] using
      LinearEquiv.det_conj (headChange K F hR) b.symm
  exact (congrArg LinearEquiv.det he).trans (hd.trans (headChange_det K F hR))

omit [Algebra ℂ K] in
theorem adjustedFrame_mulVec (g : GL4 K) (v : Head K) :
    (adjustedFrameHom K g).val.mulVec v =
      ((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ).val • g.val.mulVec v := by
  exact adjustedFrame_action K g v
theorem twistedCoordinates_standardEndo (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (x : Twisted K (standardPlane K)) :
    twistedCoordinates K (tensorTransport (standardEndo K F hR) x) =
      (adjustedFrameHom K (headUnit K F hR)).val.mulVec (twistedCoordinates K x) := by
  let b := standardPlaneBasis K
  let e := standardEndo K F hR
  let c : K := ((Matrix.GeneralLinearGroup.det (headUnit K F hR))⁻¹ : Kˣ).val
  have ht := tensorTransport_trivialization b e x
  have hd : ((LinearEquiv.det e)⁻¹ : Kˣ).val = c :=
    congrArg (fun u : Kˣ => u⁻¹.val) (standardEndo_det K F hR)
  calc
    twistedCoordinates K (tensorTransport e x) =
        b.equivFun (tensorTrivialization b (tensorTransport e x)) := rfl
    _ = b.equivFun (((LinearEquiv.det e)⁻¹ : Kˣ).val • e (tensorTrivialization b x)) :=
      congrArg b.equivFun ht
    _ = b.equivFun (c • e (tensorTrivialization b x)) :=
      congrArg (fun a : K => b.equivFun (a • e (tensorTrivialization b x))) hd
    _ = c • b.equivFun (e (tensorTrivialization b x)) := b.equivFun.map_smul c _
    _ = c • (headUnit K F hR).val.mulVec (twistedCoordinates K x) :=
      congrArg (c • ·) (standardEndo_coordinates K F hR (tensorTrivialization b x))
    _ = _ := (adjustedFrame_mulVec K (headUnit K F hR) (twistedCoordinates K x)).symm

/-- Actual tensor coordinates determined by the actual cell frame. -/
def cellTensorCoordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det) :
    Twisted K (movingPlane K (standardPlane K) F) ≃ₗ[K] Head K :=
  (tensorTransport (movingCellFrame K F hR)).symm.trans (twistedCoordinates K)

/-- Literal compensated head matrix of the actual moving tensor frame. -/
def compensatedHead (F : GL3 K) (hR : IsUnit (headMatrix K F).det) : GL4 K :=
  Matrix.GeneralLinearGroup.scalar (Fin 4) ((Matrix.GeneralLinearGroup.det F)^2) *
    adjustedFrameHom K (headUnit K F hR)

theorem compensatedHead_mulVec (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (v : Head K) :
    (compensatedHead K F hR).val.mulVec v =
      ((Matrix.GeneralLinearGroup.det F)^2 : Kˣ).val •
        (adjustedFrameHom K (headUnit K F hR)).val.mulVec v := by
  change (Matrix.scalar (Fin 4) (((Matrix.GeneralLinearGroup.det F)^2 : Kˣ).val) *
    (adjustedFrameHom K (headUnit K F hR)).val).mulVec v = _
  rw [← Matrix.mulVec_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mulVec, Matrix.one_mulVec]

theorem tensorTransport_movingFrame_comparison (F : GL3 K)
    (hR : IsUnit (headMatrix K F).det) :
    (tensorTransport (movingFrame K (standardPlane K) F)).trans
      (tensorTransport (movingCellFrame K F hR)).symm =
      tensorTransport (standardEndo K F hR) := by
  rw [← tensorTransport_symm, ← tensorTransport_trans, movingFrame_comparison]

/-- Exact coordinate formula for the original actual raw moving frame.
The raw source is the coefficient extension of the original E₀. -/
theorem rawMovingFrame_coordinates (F : GL3 K) (hR : IsUnit (headMatrix K F).det)
    (x : K ⊗[ℂ] E0) :
    cellTensorCoordinates K F hR (rawMovingFrame K F x) =
      (compensatedHead K F hR).val.mulVec (rawCoordinates K x) := by
  have ht := LinearEquiv.congr_fun (tensorTransport_movingFrame_comparison K F hR)
    (rawToTwisted K x)
  change (tensorTransport (movingCellFrame K F hR)).symm
    (tensorTransport (movingFrame K (standardPlane K) F) (rawToTwisted K x)) =
      tensorTransport (standardEndo K F hR) (rawToTwisted K x) at ht
  let c : K := ((Matrix.GeneralLinearGroup.det F)^2 : Kˣ).val
  let p := tensorTransport (movingFrame K (standardPlane K) F)
  let q := tensorTransport (movingCellFrame K F hR)
  have hx : twistedCoordinates K (rawToTwisted K x) = rawCoordinates K x :=
    (twistedCoordinates K).apply_symm_apply (rawCoordinates K x)
  calc
    cellTensorCoordinates K F hR (rawMovingFrame K F x) =
        twistedCoordinates K (q.symm (c • p (rawToTwisted K x))) := rfl
    _ = twistedCoordinates K (c • q.symm (p (rawToTwisted K x))) :=
      congrArg (twistedCoordinates K) (q.symm.map_smul c _)
    _ = c • twistedCoordinates K (q.symm (p (rawToTwisted K x))) :=
      (twistedCoordinates K).map_smul c _
    _ = c • twistedCoordinates K (tensorTransport (standardEndo K F hR) (rawToTwisted K x)) :=
      congrArg (fun y => c • twistedCoordinates K y) ht
    _ = c • (adjustedFrameHom K (headUnit K F hR)).val.mulVec
        (twistedCoordinates K (rawToTwisted K x)) :=
      congrArg (c • ·) (twistedCoordinates_standardEndo K F hR (rawToTwisted K x))
    _ = c • (adjustedFrameHom K (headUnit K F hR)).val.mulVec (rawCoordinates K x) :=
      congrArg (fun v => c • (adjustedFrameHom K (headUnit K F hR)).val.mulVec v) hx
    _ = _ := (compensatedHead_mulVec K F hR (rawCoordinates K x)).symm

end M9Native.MovingConicTensorCoordinates
